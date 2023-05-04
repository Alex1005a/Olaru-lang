{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TypeCheck where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Types
import Algebra
import Expressions
import Control.Monad.Except
import Control.Monad.State
import Data.List (nub, isPrefixOf)
import Prelude hiding (foldr)
import Data.Foldable (foldr, foldrM)
import Data.Either (partitionEithers)
import Data.Functor.Identity (runIdentity)
import ExpandMap (unionWithF)
import Debug.Trace (trace, traceShowId)

data Scheme = Forall [TypeVarName] Type
  deriving (Show, Eq, Ord)

newtype TypeEnv = TypeEnv (Map.Map Name Scheme)
  deriving (Semigroup, Monoid, Show)

newtype Unique = Unique { count :: Int }

type Infer = ExceptT TypeError (State Unique)
type Subst = Map.Map TypeVarName Type

data TypeError
  = UnificationFail Type Type
  | InfiniteType TypeVarName Type
  | UnboundVariable String
  | ApplicationToNonFunction
  | IncorrectModalityContext Name Modality Modality
  | UsageModality Name Modality Int
  | InconsistentUsage Name
  | ContructorPatArgsMismatch
  deriving (Show, Eq)

runInfer :: Infer (Subst, Type) -> Either TypeError (Scheme, Subst)
runInfer m = case evalState (runExceptT m) initUnique of
  Left err  -> Left err
  Right res@(sub, _) -> Right (closeOver res, Map.filterWithKey (\k _ -> "$" `isPrefixOf` k) sub)

closeOver :: (Subst, Type) -> Scheme
closeOver (sub, ty) = normalize sc
  where sc = generalize emptyTyenv $ apply sub ty

normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (fmap snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) letters

    fv (TypeVar a)   = [a]
    fv ((_, argTy) :-> retTy) = fv argTy ++ fv retTy
    fv (CustomType _ ts) = concatMap fv ts
    fv _   = []

    normtype ((m, a) :-> b) = (m, normtype a) :-> normtype b
    normtype (CustomType n ts) = CustomType n (normtype <$> ts)
    normtype (TypeVar a) =
      case lookup a ord of
        Just x -> TypeVar x
        Nothing -> error "type variable not in signature"
    normtype a = a

initUnique :: Unique
initUnique = Unique { count = 0 }

extend :: TypeEnv -> (TypeVarName, Scheme) -> TypeEnv
extend (TypeEnv env) (x, s) = TypeEnv $ Map.insert x s env

emptyTyenv :: TypeEnv
emptyTyenv = TypeEnv Map.empty

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TypeVarName

instance Substitutable Type where
  apply s ty@(TypeVar a)     = Map.findWithDefault ty a s
  apply s ((m, argTy) :-> retTy) = (m, apply s argTy) :-> apply s retTy
  apply s (CustomType name ts) = CustomType name (map (apply s) ts)
  apply _ a       = a

  ftv (TypeVar a)       = Set.singleton a
  ftv ((_, argTy) :-> retTy) = ftv argTy `Set.union` ftv retTy
  ftv (CustomType _ ts) = foldMap ftv ts
  ftv _        = Set.empty

instance Substitutable Scheme where
  apply s (Forall as ty)   = Forall as $ apply s' ty
                            where s' = foldr Map.delete s as
  ftv (Forall as ty) = ftv ty `Set.difference` Set.fromList as

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv   = foldr (Set.union . ftv) Set.empty

instance Substitutable TypeEnv where
  apply s (TypeEnv env) = TypeEnv $ Map.map (apply s) env
  ftv (TypeEnv env) = ftv $ Map.elems env

nullSubst :: Subst
nullSubst = Map.empty

compose :: Subst -> Subst -> Subst
s1 `compose` s2 = Map.map (apply s1) s2 `Map.union` s1

unify :: (Monad a) => Type -> Type -> ExceptT TypeError a Subst
unify ((m, argTy) :-> retTy) ((m', argTy') :-> retTy') | m == m' = do
  s1 <- unify argTy argTy'
  s2 <- unify (apply s1 retTy) (apply s1 retTy')
  pure (s2 `compose` s1)
unify (TypeVar a) t = bind a t
unify t (TypeVar a) = bind a t
unify (CustomType name1 ts1) (CustomType name2 ts2)
  | name1 == name2 && length ts1 == length ts2 =
    let together = zip ts1 ts2
        go acc (t1, t2) = do
          su <- unify (apply acc t1) (apply acc t2)
          return (su <> acc)
     in foldM go mempty together
unify a b | a == b = pure nullSubst
unify t1 t2 = throwError $ UnificationFail t1 t2

bind :: (Monad a) => TypeVarName -> Type -> ExceptT TypeError a Subst
bind a t
  | t == TypeVar a     = pure nullSubst
  | occursCheck a t = throwError $ InfiniteType a t
  | otherwise       = pure $ Map.singleton a t

occursCheck ::  Substitutable a => TypeVarName -> a -> Bool
occursCheck a t = a `Set.member` ftv t

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer Type
fresh = do
  s <- get
  put s{count = count s + 1}
  pure $ TypeVar (letters !! count s)

instantiate ::  Scheme -> Infer Type
instantiate (Forall as ty) = do
  as' <- mapM (const fresh) as
  let s = Map.fromList $ zip as as'
  pure $ apply s ty

generalize :: TypeEnv -> Type -> Scheme
generalize env ty  = Forall as ty
  where as = Set.toList $ ftv ty `Set.difference` ftv env

prims :: TypeEnv
prims = TypeEnv $ Map.fromList
  [
    ("plus", Forall [] $ (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType),
    ("mult", Forall [] $ (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType),
    ("minus", Forall [] $ (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType),
    ("True", Forall [] $ CustomType "Bool"[]),
    ("False", Forall [] $ CustomType "Bool"[])
  ]

lookupEnv :: TypeEnv -> Name -> Infer (Subst, Type)
lookupEnv (TypeEnv env) x = do
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable (show x)
    Just s  -> do t <- instantiate s
                  pure (nullSubst, t)

litType :: Literal -> Type
litType (IntegerLiteral _) = PrimType IntegerType
litType (CharLiteral _) = PrimType CharType

argModality :: Type -> Modality
argModality ((m, _) :-> _) = m
argModality _ = Unrestricted

infer :: TypeEnv -> Expr () -> Infer (Subst, Type)
infer env ex = case ex of
  NameExpr x -> lookupEnv env x

  LambdaExpr x _ argM e -> do
    tv <- fresh
    let env' = env `extend` (x, Forall [] tv)
    (s, ty) <- infer env' e
    pure (s, (argM, apply s tv) :-> ty)

  ApplyExpr f arg -> do
    tv <- fresh
    (s1, funTy) <- infer env f
    (s2, argTy) <- infer (apply s1 env) arg
    s3       <- unify (apply s2 funTy) ((argModality argTy, argTy) :-> tv)
    return (s3 `compose` s2 `compose` s1, apply s3 tv)

  CaseExpr expr patterns -> do
    (s, patTy) <- infer env expr
    casesInfer <- forM patterns (inferPatternDef (apply s env))
    tv <- fresh
    (s1, _, ty) <- foldrM (\(s2, pTy2, caseTy) (s1, pTy1, ty) -> do
          subtTy <- unify ty caseTy
          patSubsTy <- unify pTy1 pTy2
          pure (s1 `compose` s2 `compose` patSubsTy `compose` subtTy, apply patSubsTy pTy1, apply subtTy ty)
        ) (nullSubst, patTy, tv) casesInfer
    pure (s1, ty)

  LitExpr l  -> pure (nullSubst, litType l)

inferPatternDef :: TypeEnv -> (Pattern, Expr ()) -> Infer (Subst, Type, Type)
inferPatternDef  env (pat, caseExpr) = do
  (newEnv, patTy) <- inspectPattern env pat
  (s, retTy) <- infer newEnv caseExpr
  pure (s, apply s patTy, apply s retTy)

inspectPattern :: TypeEnv -> Pattern -> Infer (TypeEnv, Type)
inspectPattern env pat = case pat of
  Default -> (env,) <$> fresh
  LiteralPattern lit -> pure (env, litType lit)
  ConstructorPattern conName pats -> do
    (_, conTy) <- lookupEnv env conName
    zipWithNames env conTy pats

zipWithNames :: TypeEnv -> Type -> [Name] -> Infer (TypeEnv, Type)
zipWithNames env ((_, argTy) :-> retTy) (name : restNames) =
  zipWithNames (env `extend` (name, Forall [] argTy)) retTy restNames
zipWithNames env ty [] = pure (env, ty)
zipWithNames _ _ _ = throwError ContructorPatArgsMismatch

inferExpr :: TypeEnv -> Expr () -> Either TypeError (Scheme, Subst)
inferExpr env = runInfer . infer env

extendWithAllDefs :: TypeEnv -> [Name] -> TypeEnv
extendWithAllDefs env [] = env
extendWithAllDefs env (name : rest) =
  extendWithAllDefs env rest `extend` (name, Forall [] $ TypeVar $ "$" ++ name)

unionWithUnify :: Subst -> Subst -> Either TypeError Subst
unionWithUnify sub1 sub2 =
  runIdentity $ runExceptT $ unionWithF (\ty1 ty2 -> do
      s <- unify ty1 ty2
      pure (apply s ty1)) sub1 sub2

inferTop :: Subst -> TypeEnv -> [(Name, Expr ())] -> Either TypeError TypeEnv
inferTop _ env [] = Right env
inferTop sub env ((name, expr) : xs) = case inferExpr env expr of
  Left err -> Left err
  Right (sch@(Forall _ ty), currSub) -> do
    newSub <- unionWithUnify sub currSub
    case Map.lookup ("$" ++ name) newSub of
      Just sTy -> void $ runExcept $ unify sTy ty
      Nothing -> pure ()
    inferTop newSub (extend env (name, sch)) xs

runInferTop :: [(Name, Expr ())] -> Either TypeError TypeEnv
runInferTop defs = inferTop nullSubst (extendWithAllDefs prims $ map fst defs) defs
