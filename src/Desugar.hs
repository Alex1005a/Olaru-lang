{-# LANGUAGE TupleSections #-}
module Desugar where
import qualified Parser as P
import qualified Data.Map as Map
import Expressions (Expr (NameExpr, LambdaExpr, LitExpr, ApplyExpr, CaseExpr), Name)
import Algebra (Modality(Unrestricted))
import Data.Foldable (foldl')
import Data.Bifunctor (second)
import Types (Type ((:->), PrimType, TypeVar, CustomType))
import Control.Monad (replicateM)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import TypeCheck (Scheme, TypeError (UnboundVariable), generalize, emptyTyenv)
import Control.Monad.Except (throwError)

type ConstructorMap = Map.Map Name Scheme

type Defs = [(Name, Expr ())]

type Subst = Map.Map P.TypeVar Type

desugarExpr :: P.SugarExpr -> Expr ()
desugarExpr (P.NameExpr name) = NameExpr name
desugarExpr (P.LitExpr litt) = LitExpr litt
desugarExpr (P.LambdaExpr args sexpr) = do
  let expr = desugarExpr sexpr in
    foldr (\(arg, m) -> LambdaExpr arg () m) expr args
desugarExpr (P.ApplyExpr fun args) = do
  let funExpr = desugarExpr fun
      argExprs = desugarExpr <$> args in
    foldl' ApplyExpr funExpr argExprs
desugarExpr (P.CaseExpr sexpr patterns) =
  let expr = desugarExpr sexpr
      desugaredPats = second desugarExpr <$> patterns in
    CaseExpr expr desugaredPats

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

desugarTypeVar :: P.TypeVar -> Type
desugarTypeVar tyVar = TypeVar $ fromIntegral $ fromJust $ elemIndex tyVar letters

desugarType :: Subst -> P.Type -> Either TypeError Type
desugarType subst (dargTy P.::-> dretTy) = do
  argTy <- desugarType subst dargTy
  retTy <- desugarType subst dretTy
  pure $ (Unrestricted, argTy) :-> retTy
desugarType _ (P.PrimType p) = pure $ PrimType p
desugarType subst (P.TypeVar tyVar) = case Map.lookup tyVar subst of
  Nothing -> throwError $ UnboundVariable tyVar
  Just ty -> pure ty
desugarType subst (P.CustomType tyName types) = do
  desugTypes <- mapM (desugarType subst) types
  pure $ CustomType tyName desugTypes

typeFromConDef :: Subst -> P.ConstructorDefinition -> Type -> Either TypeError (Name, Type)
typeFromConDef subst (P.ConstructorDefinition conName types) ret = do
  argTypes <- mapM (fmap (Unrestricted,) . desugarType subst) types
  pure (conName, foldr (:->) ret argTypes)

desugar :: P.AST -> Either TypeError (Defs, ConstructorMap)
desugar [] = pure ([], Map.empty)
desugar (def : restAst) = do
  (exprs, conMap) <- desugar restAst
  case def of
    P.ValueDefinition (P.NameDefinition name sexpr) -> pure ((name, desugarExpr sexpr) : exprs, conMap)
    P.DataDefinition dataName styVars conDefs -> do
      let substList = (\tyVar -> (tyVar, desugarTypeVar tyVar)) <$> styVars
      let retTy = CustomType dataName (snd <$> substList)
      let subst = Map.fromList substList
      conTypes <- mapM (\conDef -> second (generalize emptyTyenv) <$> typeFromConDef subst conDef retTy) conDefs
      pure (exprs, conMap `Map.union` Map.fromList conTypes)
