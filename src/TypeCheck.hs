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
import SortDefs (sortDefs)
import Control.Monad.Except
import Control.Monad.State
import Data.List (nub)
import Prelude hiding (foldr)
import Data.Foldable (foldr, foldrM)
import Data.Bifunctor (first)

data Scheme = Forall [TypeVarName] Type
  deriving (Show, Eq, Ord)

newtype TypeEnv = TypeEnv (Map.Map Name Scheme)
  deriving (Semigroup, Monoid, Show)

newtype Unique = Unique { count :: Int }

type Infer = ExceptT TypeError (State (Subst, Unique))
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

runInfer :: Infer Type -> Either TypeError Scheme
runInfer m = case runState (runExceptT m) (nullSubst, initUnique) of
  (Left err, _)  -> Left err
  (Right ty, (s, _)) -> Right (closeOver (s, ty))

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

union :: TypeEnv -> TypeEnv -> TypeEnv
union (TypeEnv env1) (TypeEnv env2) = TypeEnv $ Map.union env1 env2

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

mgu :: (Monad a) => Type -> Type -> ExceptT TypeError a Subst
mgu ((m, argTy) :-> retTy) ((m', argTy') :-> retTy') | m == m' = do
  s1 <- mgu argTy argTy'
  s2 <- mgu (apply s1 retTy) (apply s1 retTy')
  pure (s2 `compose` s1)
mgu (TypeVar a) t = bind a t
mgu t (TypeVar a) = bind a t
mgu (CustomType name1 ts1) (CustomType name2 ts2)
  | name1 == name2 && length ts1 == length ts2 =
    let together = zip ts1 ts2
        go acc (t1, t2) = do
          su <- mgu (apply acc t1) (apply acc t2)
          return (su `compose` acc)
     in foldM go nullSubst together
mgu a b | a == b = pure nullSubst
mgu t1 t2 = throwError $ UnificationFail t1 t2

bind :: (Monad a) => TypeVarName -> Type -> ExceptT TypeError a Subst
bind a t
  | t == TypeVar a     = pure nullSubst
  | occursCheck a t = throwError $ InfiniteType a t
  | otherwise       = pure $ Map.singleton a t

occursCheck ::  Substitutable a => TypeVarName -> a -> Bool
occursCheck a t = a `Set.member` ftv t

getSubst :: Infer Subst
getSubst = gets fst

extSubst :: Subst -> Infer ()
extSubst s1 =
  modify (first (compose s1))

unify      :: Type -> Type -> Infer ()
unify t1 t2 = do
  s <- getSubst
  u <- mgu (apply s t1) (apply s t2)
  extSubst u

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer Type
fresh = do
  (s, u) <- get
  put (s, u{count = count u + 1})
  pure $ TypeVar (letters !! count u)

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

lookupEnv :: TypeEnv -> Name -> Infer Type
lookupEnv (TypeEnv env) x = do
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable (show x)
    Just s  -> do instantiate s

litType :: Literal -> Type
litType (IntegerLiteral _) = PrimType IntegerType
litType (CharLiteral _) = PrimType CharType

argModality :: Type -> Modality
argModality ((m, _) :-> _) = m
argModality _ = Unrestricted

infer :: TypeEnv -> Expr () -> Infer Type
infer env ex = case ex of
  NameExpr x -> lookupEnv env x

  LambdaExpr x _ argM e -> do
    tv <- fresh
    let env' = env `extend` (x, Forall [] tv)
    ty <- infer env' e
    pure ((argM, tv) :-> ty)

  ApplyExpr f arg -> do
    tv <- fresh
    funTy <- infer env f
    argTy <- infer env arg
    unify ((argModality argTy, argTy) :-> tv) funTy
    return tv

  CaseExpr expr patterns -> do
    patTy <- infer env expr
    casesInfer <- forM patterns (inferPatternDef env)
    tv <- fresh
    (_, ty) <- foldrM (\(patTy2, caseTy) (patTy1, ty) -> do
          unify ty caseTy
          unify patTy1 patTy2
          pure (patTy1, ty)
        ) (patTy, tv) casesInfer
    pure ty

  LitExpr l  -> pure $ litType l

inferPatternDef :: TypeEnv -> (Pattern, Expr ()) -> Infer (Type, Type)
inferPatternDef  env (pat, caseExpr) = do
  (newEnv, patTy) <- inspectPattern env pat
  retTy <- infer newEnv caseExpr
  pure (patTy, retTy)

inspectPattern :: TypeEnv -> Pattern -> Infer (TypeEnv, Type)
inspectPattern env pat = case pat of
  Default -> (env,) <$> fresh
  LiteralPattern lit -> pure (env, litType lit)
  ConstructorPattern conName pats -> do
    conTy <- lookupEnv env conName
    zipWithNames env conTy pats

zipWithNames :: TypeEnv -> Type -> [Name] -> Infer (TypeEnv, Type)
zipWithNames env ((_, argTy) :-> retTy) (name : restNames) =
  zipWithNames (env `extend` (name, Forall [] argTy)) retTy restNames
zipWithNames env ty [] = pure (env, ty)
zipWithNames _ _ _ = throwError ContructorPatArgsMismatch

inferExpr :: TypeEnv -> Expr () -> Either TypeError Scheme
inferExpr env = runInfer . infer env

inferTop :: TypeEnv -> [(Name, Expr ())] -> Infer [(Name, Type)]
inferTop env defs = do
  ts <- mapM (const fresh) defs
  let scs = map (Forall []) ts
      is = map fst defs
      extEnv = env `union` TypeEnv (Map.fromList $ zip is scs)
  let exprs = map snd defs
  types <- mapM (infer extEnv) exprs
  zipWithM_ unify ts types
  pure $ zip is types

runInferMutualTop :: TypeEnv -> [(Name, Expr ())] -> Either TypeError [(Name, Scheme)]
runInferMutualTop env defs = do
  let inferDefs = inferTop env defs
  case runState (runExceptT inferDefs) (nullSubst, initUnique) of
    (Left err, _)  -> Left err
    (Right defsSchemed, (s, _)) -> Right ((\(n, ty) -> (n, closeOver (s, ty))) <$> defsSchemed)

runInferSeq :: TypeEnv -> [[(Name, Expr ())]] -> Either TypeError [(Name, Scheme)]
runInferSeq env (defs : rest) = do
  types <- runInferMutualTop env defs
  restTypes <- runInferSeq (env `union` TypeEnv (Map.fromList types)) rest
  pure $ types ++ restTypes
runInferSeq _ [] = pure []
