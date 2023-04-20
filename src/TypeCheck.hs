{-# LANGUAGE TupleSections #-}
module TypeCheck where
import Data.Map (Map, fromList, insert, empty, findWithDefault, singleton, union, lookup)
import Types
import Algebra (Modality (Unrestricted, Linear, Affine, Relevant), mult, more)
import Control.Monad (zipWithM, when, unless)
import Expressions
import Prelude hiding (lookup)
import Control.Applicative ((<|>))

type EnvType = Map Name Type

type LocalEnvType = Map Name (Type, Modality)

data TypeError
  = TypeMismatch Type Type
  | UnboundName Name
  deriving (Eq, Show)

prims :: EnvType
prims = fromList
    [
        ("plus", (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType),
        ("mult", (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType),
        ("minus", (Unrestricted, PrimType IntegerType) :-> (Unrestricted, PrimType IntegerType) :-> PrimType IntegerType)
    ]

zipNamesWithTypes :: Type -> [Name] -> Maybe (LocalEnvType, Type)
zipNamesWithTypes ((m, argTy) :-> retTy) (name : rest) = do
    (restLocEnv, ty) <- zipNamesWithTypes retTy rest
    pure (insert name (argTy, m) restLocEnv, ty)
zipNamesWithTypes ty [] = case ty of
    (_ :-> _) -> Nothing
    _ -> Just (empty, ty)
zipNamesWithTypes _ _ = Nothing

subst :: Type -> Map Name Type -> Type
subst ty@(TypeVar name) substEnv = findWithDefault ty name substEnv
subst (CustomType n args) substEnv =
    CustomType n $ fmap (`subst` substEnv) args
subst ((m, ty) :-> ret) substEnv = (m, subst ty substEnv) :-> subst ret substEnv
subst other _ = other

makeSubstMap :: Type -> Type -> Maybe (Map Name Type)
makeSubstMap (TypeVar name) ty = pure $ singleton name ty
makeSubstMap (CustomType n args) (CustomType name substArgs) =
    if n /= name then Nothing else do
        substMaps <- zipWithM makeSubstMap args substArgs
        pure $ foldr union empty substMaps
makeSubstMap ((m1, argTy) :-> ret) ((m2, argTy1) :-> ret1) = do
    if m1 /= m2 then Nothing else do
        argSubstMap <- makeSubstMap argTy argTy1
        retSubstMap <- makeSubstMap ret ret1
        pure $ union argSubstMap retSubstMap
makeSubstMap (PrimType primTy) (PrimType ty) =
    if ty == primTy then pure empty else Nothing
makeSubstMap _ (TypeVar _) = pure empty
makeSubstMap _ _ = Nothing

typeCheckPattern :: Type -> (Pattern, Expr) -> Modality -> EnvType -> LocalEnvType -> Maybe (Type, [Name])
typeCheckPattern _ (Default, expr) m env localEnv = typeCheck expr m env localEnv
typeCheckPattern (PrimType IntegerType) (LiteralPattern (IntegerLiteral _), expr) m env localEnv = typeCheck expr m env localEnv
typeCheckPattern (PrimType CharType) (LiteralPattern (CharLiteral _), expr) m env localEnv = typeCheck expr m env localEnv
typeCheckPattern (CustomType name typeArgs) (ConstructorPattern conName args, expr) m env localEnv = do
    conType <- lookup conName env
    (CustomType tyName oldArgs) <- pure $ retType conType
    when (tyName /= name) Nothing
    maps <- zipWithM makeSubstMap oldArgs typeArgs
    let substMapForCon = foldr union empty maps
    (vars, _) <- zipNamesWithTypes (subst conType substMapForCon) args
    typeCheck expr m env (vars `union` localEnv)
typeCheckPattern _ _ _ _ _ = Nothing

typeCheckPatterns :: Type -> [(Pattern, Expr)] -> Modality -> EnvType -> LocalEnvType -> Maybe (Type, [Name])
typeCheckPatterns ty [casePat] m env localEnv = typeCheckPattern ty casePat m env localEnv
typeCheckPatterns ty (casePat : rest) m env localEnv = do
    retTy <- typeCheckPattern ty casePat m env localEnv
    restTy <- typeCheckPatterns ty rest m env localEnv
    if fst retTy == fst restTy then Just retTy else Nothing
typeCheckPatterns _ _ _ _ _ = Nothing

typeCheck :: Expr -> Modality -> EnvType -> LocalEnvType -> Maybe (Type, [Name])
typeCheck (LitExpr lit) _ _ _ = case lit of
    IntegerLiteral _ -> Just (PrimType IntegerType, [])
    CharLiteral _ -> Just (PrimType CharType, [])
typeCheck (ApplyExpr expr arg) m env localEnv = do
    ((argModality, argTy) :-> ret, usageExpr) <- typeCheck expr m env localEnv
    (argType, usageArg) <- typeCheck arg (mult argModality m) env localEnv
    newRetTy <- subst ret <$> makeSubstMap argTy argType
    Just (newRetTy, usageArg ++ usageExpr)
typeCheck (LambdaExpr arg argType m expr) _ env localEnv = do
    (retTy, usage) <- typeCheck expr Linear env (insert arg (argType, m) localEnv)
    let countUsage = length $ filter (== arg) usage
    case m of
      Unrestricted -> pure ()
      Linear -> when (countUsage /= 1) Nothing
      Affine -> when (countUsage > 1) Nothing
      Relevant -> when (countUsage == 0) Nothing
    Just ((m, argType) :-> retTy, usage)
typeCheck (CaseExpr expr patterns) ts env localEnv = do
    (ty, usage) <- typeCheck expr ts env localEnv
    (\(retTy, us) -> (retTy , us ++ usage)) <$> typeCheckPatterns ty patterns ts env localEnv
typeCheck (NameExpr name) ts env localEnv = (do
        (ty, nameTS) <- lookup name localEnv
        unless (more ts nameTS) Nothing
        pure (ty, [name]))
    <|> fmap (, []) (lookup name env)
