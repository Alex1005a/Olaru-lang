{-# LANGUAGE TupleSections #-}
module ModalCheck where

import Expressions (Name, Expr (NameExpr, ApplyExpr, LambdaExpr, LitExpr, CaseExpr), Pattern (ConstructorPattern))
import Algebra (Modality (Unrestricted, Linear, Affine, Relevant, Zero), more, mult)
import Data.Map (Map, lookup, insert, fromList, union, toList, filterWithKey, mapWithKey, empty, map)
import TypeCheck (TypeError (IncorrectModalityContext, UnboundVariable, ApplicationToNonFunction, UsageModality, InconsistentUsage), litType, Scheme (Forall), prims, TypeEnv (TypeEnv))
import Control.Monad (unless, when)
import Control.Monad.Except (throwError, ExceptT, runExceptT)
import Prelude hiding (lookup)
import Types (Type ((:->)), funArgs)
import Control.Monad.Reader (Reader, asks, runReader)
import Control.Applicative ((<|>))
import Data.Maybe (fromJust)
import Data.List (groupBy, sortBy)
import Data.Ord (comparing)
import Data.Function (on)
import Data.Bifunctor (second)

type Usage = [Name]

type LocalEnv = Map Name (Type, Modality)

type EnvDef = Map Name (Type, Modality)

type Check = ExceptT TypeError (Reader EnvDef)

throwFromMaybe :: TypeError -> Maybe a -> Check a
throwFromMaybe _ (Just b) = pure b
throwFromMaybe a Nothing = throwError a

checkUsageCount :: Modality -> Name -> Usage -> Check ()
checkUsageCount m name usage = do
    let countUsage = length $ filter (== name) usage
    let usageErr = UsageModality name m countUsage
    case m of
      Unrestricted -> pure ()
      Linear -> when (countUsage /= 1) $ throwError usageErr
      Affine -> when (countUsage > 1) $ throwError usageErr
      Relevant -> when (countUsage == 0) $ throwError usageErr
      Zero -> when (countUsage /= 0) $ throwError usageErr

groupByFst :: (Ord a) => [(a, b)] -> [[(a, b)]]
groupByFst = groupBy ((==) `on` fst)
           . sortBy (comparing fst)

data ArgUsage = UseAny | Use0 | Use1 | UseAff | UseRel

argUsageToModality :: ArgUsage -> Modality
argUsageToModality UseAny = Unrestricted
argUsageToModality Use0 = Zero
argUsageToModality Use1 = Linear
argUsageToModality UseAff = Affine
argUsageToModality UseRel = Relevant

combineArgUsage :: (Name, ArgUsage) -> (Name, ArgUsage) -> Check (Name, ArgUsage)
combineArgUsage (_, UseAny) u = pure u
combineArgUsage u (_, UseAny) = pure u
combineArgUsage (_, Use0) (n, Use1) = throwError (InconsistentUsage n)
combineArgUsage (n, Use1) (_, Use0) = throwError (InconsistentUsage n)
combineArgUsage (_, Use0) (n, UseRel) = throwError (InconsistentUsage n)
combineArgUsage (n, UseRel) (_, Use0) = throwError (InconsistentUsage n)
combineArgUsage (n, Use1) _ = pure (n, Use1)
combineArgUsage _ (n, Use1) = pure (n, Use1)
combineArgUsage (n, Use0) (_, UseAff) = pure (n, Use0)
combineArgUsage (_, UseAff) (n, Use0) = pure (n, Use0)
combineArgUsage (n, UseRel) (_, UseAff) = pure (n, Use1)
combineArgUsage (_, UseAff) (n, UseRel) = pure (n, Use1)
combineArgUsage u _ = pure u

combineUsages :: [(Name, ArgUsage)] -> Check (Name, ArgUsage)
combineUsages [] = error "combineUsages arg empty"
combineUsages [x] = pure x
combineUsages (x : xs) = do
  rest <- combineUsages xs
  combineArgUsage x rest

locsArgUsage :: Name -> Modality -> Usage -> Check ArgUsage
locsArgUsage name m used = do
    let countUsage = length $ filter (== name) used
    let usageErr = UsageModality name m countUsage
    case m of
      Unrestricted -> pure UseAny
      Linear -> do
        when (countUsage > 1) $ throwError usageErr
        pure $ if countUsage == 1 then Use0 else Use1
      Affine -> do
        when (countUsage > 1) $ throwError usageErr
        pure $ if countUsage == 1 then Use0 else UseAff
      Relevant -> pure $ if countUsage == 0 then UseRel else UseAny
      Zero -> do
        when (countUsage /= 0) $ throwError usageErr
        pure Use0

checkCase :: Modality -> (Pattern, Expr Type) -> LocalEnv -> Check (Type, [(Name, ArgUsage)])
checkCase m (pat, caseExpr) locEnv = do
    newLocs <- case pat of
      ConstructorPattern conName args -> do
        conLookup <- asks $ lookup conName
        (conTy, conM) <- throwFromMaybe (UnboundVariable conName) conLookup
        unless (more m conM) $ throwError (IncorrectModalityContext conName m conM)
        pure $ zip args $ funArgs conTy
      _ -> pure []
    (ty, used, newLocEnv) <- mcheck m (union locEnv $ fromList newLocs) caseExpr
    mapM_ (\(argName, _) -> checkUsageCount (snd $ fromJust $ lookup argName newLocEnv) argName used) newLocs
    argUsage <- mapM (\(locName, (_, locM)) -> (locName,) <$> locsArgUsage locName locM used)
      $ filter (`notElem` newLocs) $ toList newLocEnv
    pure (ty, argUsage)

mcheck :: Modality -> LocalEnv -> Expr Type -> Check (Type, Usage, LocalEnv)
mcheck m locEnv (NameExpr name) = do
    defLookup <- asks $ lookup name
    let lookupResult = ((, [name]) <$> lookup name locEnv) <|> ((, []) <$> defLookup)
    ((ty, varM), usage) <- throwFromMaybe (UnboundVariable name) lookupResult
    unless (more m varM) $ throwError (IncorrectModalityContext name m varM)
    pure (ty, usage, locEnv)
mcheck m locEnv (ApplyExpr fun arg) = do
    (funTy, funUsed, funNewEnv) <- mcheck m locEnv fun
    case funTy of
        ((am, _) :-> retTy) -> do
            (_, argUsed, argNewEnv) <- mcheck (mult am m) funNewEnv arg
            pure (retTy, funUsed ++ argUsed, argNewEnv)
        _ -> throwError ApplicationToNonFunction
mcheck _ locEnv (LambdaExpr argName argTy argM expr) = do
    (retTy, used, newLocEnv) <- mcheck argM (insert argName (argTy, argM) locEnv) expr
    checkUsageCount (snd $ fromJust $ lookup argName newLocEnv) argName used
    pure ((argM, argTy) :-> retTy, filter (/= argName) used, filterWithKey (\k _ -> k /= argName) newLocEnv)
mcheck _ locEnv (LitExpr l) = pure (litType l, [], locEnv)
mcheck m locEnv (CaseExpr matchExpr pats) = do
    (_, matchUsed, newLocEnv) <- mcheck m locEnv matchExpr
    caseCheckedWithTy <- traverse (\pe -> checkCase m pe newLocEnv) pats
    let ty = fst $ head caseCheckedWithTy
    let caseChecked = groupByFst $ concatMap snd caseCheckedWithTy
    newLocList <- mapM combineUsages caseChecked
    let newLoc = fromList $ second argUsageToModality <$> newLocList
    pure (ty, matchUsed, mapWithKey (\n (t, _) -> (t, fromJust $ lookup n newLoc)) locEnv)

runMcheck :: [(Name, Expr Type, Scheme)] -> Either TypeError [(Type, Usage, LocalEnv)]
runMcheck defs =
  let envDef = fromList $ (\(n, _, Forall _ ty) -> (n, (ty, Unrestricted))) <$> defs in
  let checkDefs = mapM (mcheck Linear empty) ((\(_, exprTy, _) -> exprTy) <$> defs) in
  let TypeEnv primsModal = prims in
    let primsModal' = Data.Map.map (\(Forall _ ty) -> (ty, Unrestricted)) primsModal in
  runReader (runExceptT checkDefs) (primsModal' `union` envDef)