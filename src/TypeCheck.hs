{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TypeCheck where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Types
import Algebra
import Expressions ( Expr(..), Literal(..), Name, Pattern(..) )
import SortDefs (MutualDefs)
import Control.Monad.Except
    ( ExceptT,
      foldM,
      zipWithM_,
      forM,
      MonadError(throwError),
      runExceptT )
import Control.Monad.State
    ( State, gets, modify, runState, MonadState(put, get) )
import Data.Foldable (foldrM)
import Data.Bifunctor (first)
import GHC.Natural (Natural)

data Scheme = Forall [TypeVar] Type
  deriving (Show, Eq, Ord)

schemeArity :: Scheme -> Int
schemeArity (Forall _ ty) = arity ty

newtype TypeEnv = TypeEnv (Map.Map Name Scheme)
  deriving (Semigroup, Monoid, Show)

newtype Unique = Unique { count :: Natural }

type Infer = ExceptT TypeError (State (Subst, Unique))
type Subst = Map.Map TypeVar Type

data TypeError
  = UnificationFail Type Type
  | InfiniteType TypeVar Type
  | UnboundVariable String
  | ApplicationToNonFunction
  | IncorrectModalityContext Name Modality Modality
  | UsageModality Name Modality Int
  | InconsistentUsage Name
  | ContructorPatArgsMismatch
  deriving (Show, Eq)

closeOver :: (Subst, Type) -> Scheme
closeOver (sub, ty) = normalize $ apply sub ty

normalize :: Type -> Scheme
normalize ty = Forall (fmap snd ord) (normtype ty)
  where
    ord = zip (Set.toList $ ftv ty) [0..]

    normtype ((m, a) :-> b) = (m, normtype a) :-> normtype b
    normtype (CustomType n ts) = CustomType n (normtype <$> ts)
    normtype (TypeVar a) =
      case lookup a ord of
        Just x -> TypeVar x
        Nothing -> error "type variable not in signature"
    normtype a = a

initUnique :: Unique
initUnique = Unique { count = 0 }

extend :: TypeEnv -> (Name, Scheme) -> TypeEnv
extend (TypeEnv env) (x, s) = TypeEnv $ Map.insert x s env

union :: TypeEnv -> TypeEnv -> TypeEnv
union (TypeEnv env1) (TypeEnv env2) = TypeEnv $ Map.union env1 env2

emptyTyenv :: TypeEnv
emptyTyenv = TypeEnv Map.empty

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TypeVar

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

bind :: (Monad a) => TypeVar -> Type -> ExceptT TypeError a Subst
bind a t
  | t == TypeVar a     = pure nullSubst
  | occursCheck a t = throwError $ InfiniteType a t
  | otherwise       = pure $ Map.singleton a t

occursCheck ::  Substitutable a => TypeVar -> a -> Bool
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

fresh :: Infer Type
fresh = do
  (s, u) <- get
  put (s, u{count = count u + 1})
  pure $ TypeVar $ count u

instantiate :: Scheme -> Infer Type
instantiate (Forall as ty) = do
  as' <- mapM (const fresh) as
  let s = Map.fromList $ zip as as'
  pure $ apply s ty

generalize :: TypeEnv -> Type -> Scheme
generalize env ty  = Forall as ty
  where as = Set.toList $ ftv ty `Set.difference` ftv env

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

infer :: TypeEnv -> Expr () -> Infer (Expr Type, Type)
infer env ex = case ex of
  NameExpr x -> (NameExpr x,) <$> lookupEnv env x

  LambdaExpr x _ argM e -> do
    tv <- fresh
    let env' = env `extend` (x, Forall [] tv)
    (eTy, ty) <- infer env' e
    pure (LambdaExpr x tv argM eTy, (argM, tv) :-> ty)

  ApplyExpr f arg -> do
    tv <- fresh
    (funExpr, funTy) <- infer env f
    (argExpr, argTy )<- infer env arg
    unify ((argModality argTy, argTy) :-> tv) funTy
    return (ApplyExpr funExpr argExpr, tv)

  CaseExpr expr patterns -> do
    (matchExpr, patTy) <- infer env expr
    casesInfer <- forM patterns (inferPatternDef env)
    tv <- fresh
    (_, ty) <- foldrM (\(patTy2, caseTy) (patTy1, ty) -> do
          unify ty caseTy
          unify patTy1 patTy2
          pure (patTy1, ty)
        ) (patTy, tv) $ (\(a, r, _) -> (a, r)) <$> casesInfer
    pure (CaseExpr matchExpr (zipWith (\(_, _, t) (p, _) -> (p, t)) casesInfer patterns), ty )

  LitExpr l -> pure (LitExpr l, litType l)

inferPatternDef :: TypeEnv -> (Pattern, Expr ()) -> Infer (Type, Type, Expr Type)
inferPatternDef  env (pat, caseExpr) = do
  (newEnv, patTy) <- inspectPattern env pat
  (retExpr, retTy) <- infer newEnv caseExpr
  pure (patTy, retTy, retExpr)

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

prims :: TypeEnv
prims = TypeEnv $ Map.fromList
  [
    ("plus", Forall [] $ (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType),
    ("mult", Forall [] $ (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType),
    ("minus", Forall [] $ (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType),
    ("True", Forall [] $ CustomType "Bool" []),
    ("False", Forall [] $ CustomType "Bool" [])
  ]

typeScheme :: TypeEnv -> Expr Type -> Infer (Expr Scheme)
typeScheme env expr = case expr of
  LitExpr litt -> return (LitExpr litt)
  NameExpr n -> return (NameExpr n)
  ApplyExpr e1 e2 -> ApplyExpr <$> typeScheme env e1 <*> typeScheme env e2
  LambdaExpr n ty m retExpr -> do
    s <- getSubst
    let sch = generalize env (apply s ty)
    exprSh <- typeScheme (env `extend` (n, sch)) retExpr
    return (LambdaExpr n sch m exprSh)
  CaseExpr e patDefs -> CaseExpr <$> typeScheme env e <*> forM patDefs (schemePatternDef env)

schemePatternDef :: TypeEnv -> (Pattern, Expr Type) -> Infer (Pattern, Expr Scheme)
schemePatternDef env (pat, expr) = (pat,) <$> typeScheme env expr

inferTop :: TypeEnv -> [(Name, Expr ())] -> Infer [(Name, Expr Scheme, Type)]
inferTop env defs = do
  ts <- mapM (const fresh) defs
  let scs = map (Forall []) ts
      is = map fst defs
      extEnv = env `union` TypeEnv (Map.fromList $ zip is scs)
  let exprs = map snd defs
  inferResult <- mapM (infer extEnv) exprs
  let (typesExprs, types) = unzip inferResult
  zipWithM_ unify ts types
  schExprs <- traverse (typeScheme extEnv) typesExprs
  pure $ zip3 is schExprs types

runInferMutualTop :: TypeEnv -> MutualDefs () -> Either TypeError [(Name, Expr Scheme, Scheme)]
runInferMutualTop env defs = do
  let inferDefs = inferTop env defs
  case runState (runExceptT inferDefs) (nullSubst, initUnique) of
    (Left err, _)  -> Left err
    (Right defsSchemed, (s, _)) -> Right ((\(n, exprTy, ty) -> (n, exprTy, closeOver (s, ty))) <$> defsSchemed)

runInferSeq :: TypeEnv -> [MutualDefs ()] -> Either TypeError [(Name, Expr Scheme, Scheme)]
runInferSeq env (defs : rest) = do
  types <- runInferMutualTop env defs
  restTypes <- runInferSeq (env `union` TypeEnv (Map.fromList ((\(n, _, sch) -> (n, sch)) <$> types))) rest
  pure $ types ++ restTypes
runInferSeq _ [] = pure []
