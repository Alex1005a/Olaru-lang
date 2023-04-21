{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TypeCheck where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Types
import Algebra (Modality (Unrestricted, Linear, Affine, Relevant), mult, more)
import Control.Monad (zipWithM, when, unless)
import Expressions
import Control.Applicative ((<|>))
import Control.Monad.Except
import Control.Monad.State
import Data.List (nub)
import Prelude hiding (foldr)
import Data.Foldable (foldr)

data Scheme = Forall [TypeVarName] Type
  deriving (Show, Eq, Ord)


newtype TypeEnv = TypeEnv (Map.Map Name (Modality, Scheme))
  deriving (Semigroup, Monoid)

data Unique = Unique { count :: Int }

type Infer = ExceptT TypeError (State Unique)
type Subst = Map.Map TypeVarName Type

data TypeError
  = UnificationFail Type Type
  | InfiniteType TypeVarName Type
  | UnboundVariable String
  deriving (Show, Eq)

runInfer :: Infer (Subst, Type) -> Either TypeError Scheme
runInfer m = case evalState (runExceptT m) initUnique of
  Left err  -> Left err
  Right res -> Right $ closeOver res

closeOver :: (Map.Map TypeVarName Type, Type) -> Scheme
closeOver (sub, ty) = normalize sc
  where sc = generalize emptyTyenv (apply sub ty)

initUnique :: Unique
initUnique = Unique { count = 0 }

extend :: TypeEnv -> (TypeVarName, Modality, Scheme) -> TypeEnv
extend (TypeEnv env) (x, m, s) = TypeEnv $ Map.insert x (m, s) env

emptyTyenv :: TypeEnv
emptyTyenv = TypeEnv Map.empty

typeof :: TypeEnv -> TypeVarName -> Maybe (Modality, Scheme)
typeof (TypeEnv env) name = Map.lookup name env

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TypeVarName

instance Substitutable Type where
  apply s t@(TypeVar a)     = Map.findWithDefault t a s
  apply s ((m, t1) :-> t2) = (m, apply s t1) :-> apply s t2
  apply _ a       = a

  ftv (TypeVar a)       = Set.singleton a
  ftv ((_, t1) :-> t2) = ftv t1 `Set.union` ftv t2
  ftv _        = Set.empty

instance Substitutable Scheme where
  apply s (Forall as t)   = Forall as $ apply s' t
                            where s' = foldr Map.delete s as
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv   = foldr (Set.union . ftv) Set.empty

instance Substitutable TypeEnv where
  apply s (TypeEnv env) =  TypeEnv $ Map.map (\(m, ty) -> (m, apply s ty)) env
  ftv (TypeEnv env) = ftv $ Map.elems $ Map.map snd env


nullSubst :: Subst
nullSubst = Map.empty

compose :: Subst -> Subst -> Subst
s1 `compose` s2 = Map.map (apply s1) s2 `Map.union` s1

unify ::  Type -> Type -> Infer Subst
unify ((m, l) :-> r) ((m', l') :-> r')  = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  return (s2 `compose` s1)

unify (TypeVar a) t = bind a t
unify t (TypeVar a) = bind a t
unify a b | a == b = return nullSubst
unify t1 t2 = throwError $ UnificationFail t1 t2

bind ::  TypeVarName -> Type -> Infer Subst
bind a t
  | t == TypeVar a     = return nullSubst
  | occursCheck a t = throwError $ InfiniteType a t
  | otherwise       = return $ Map.singleton a t

occursCheck ::  Substitutable a => TypeVarName -> a -> Bool
occursCheck a t = a `Set.member` ftv t

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer Type
fresh = do
  s <- get
  put s{count = count s + 1}
  return $ TypeVar (letters !! count s)

instantiate ::  Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const fresh) as
  let s = Map.fromList $ zip as as'
  return $ apply s t

generalize :: TypeEnv -> Type -> Scheme
generalize env t  = Forall as t
  where as = Set.toList $ ftv t `Set.difference` ftv env

prims :: Name -> Maybe Type
prims name = case name of
    "plus" -> pure $ (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType
    "mult" -> pure $ (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType
    "minus" -> pure $ (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType
    _ -> Nothing

lookupEnv :: TypeEnv -> Name -> Infer (Modality, Type)
lookupEnv (TypeEnv env) x =
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable (show x)
    Just (m, s)  -> 
               do t <- instantiate s
                  return (m, t)

infer :: TypeEnv -> Modality -> Expr () -> Infer (Subst, Type)
infer env m ex = case ex of
  NameExpr x ->
    case prims x of
      Just t -> return (nullSubst, t)
      Nothing -> do
        (modal, t) <- lookupEnv env x
        unless (more modal m) $ error "incorrect context"
        return (nullSubst, t)

  LambdaExpr x _ argM e -> do
    tv <- fresh
    let env' = env `extend` (x, m, Forall [] tv)
    (s1, t1) <- infer env' argM e
    return (s1, (argM, apply s1 tv) :-> t1)

  ApplyExpr e1 e2 -> do
    tv <- fresh
    (s1, t1) <- infer env m e1
    case t1 of
      ((argM, _) :-> _) -> do
        (s2, t2) <- infer (apply s1 env) (mult argM m) e2
        s3       <- unify (apply s2 t1) ((argM, t2) :-> tv)
        return (s3 `compose` s2 `compose` s1, apply s3 tv)
      _ -> error "err"

  LitExpr (IntegerLiteral _)  -> return (nullSubst, PrimType IntegerType)
  LitExpr (CharLiteral _) -> return (nullSubst, PrimType CharType)

inferExpr :: TypeEnv -> Expr () -> Either TypeError Scheme
inferExpr env = runInfer . infer env Linear
{-
inferPrim :: TypeEnv -> [Expr ()] -> Type -> Infer (Subst, Type)
inferPrim env l t = do
  tv <- fresh
  (s1, tf) <- foldM inferStep (nullSubst, id) l
  s2 <- unify (apply s1 (tf tv)) t
  return (s2 `compose` s1, apply s2 tv)
  where
  inferStep (s, tf) exp = do
    (s', t) <- infer (apply s env) Linear exp
    return (s' `compose` s, tf . ((undefined, t) :->))

inferTop :: TypeEnv -> [(String, Expr ())] -> Either TypeError TypeEnv
inferTop env [] = Right env
inferTop env ((name, ex):xs) = case inferExpr env ex of
  Left err -> Left err
  Right ty -> inferTop (extend env (name, ty)) xs
-}
normalize :: Scheme -> Scheme
normalize (Forall ts body) = Forall (fmap snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) letters

    fv (TypeVar a)   = [a]
    fv ((_, a) :-> b) = fv a ++ fv b
    fv _   = []

    normtype ((m, a) :-> b) = (m, normtype a) :-> (normtype b)
    normtype (TypeVar a)   =
      case lookup a ord of
        Just x -> TypeVar x
        Nothing -> error "type variable not in signature"
    normtype a = a