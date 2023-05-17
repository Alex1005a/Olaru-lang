{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
module ModalCheck where

import Expressions (Name, Expr (NameExpr, ApplyExpr, LambdaExpr, LitExpr, CaseExpr), Pattern (ConstructorPattern))
import Algebra (Modality (Unrestricted, Linear, Affine, Relevant, Zero, Ordered), more, mult)
import Data.Map (Map, lookup, insert, fromList, union, toList, filterWithKey, mapWithKey, map, empty)
import TypeCheck (TypeError (IncorrectModalityContext, UnboundVariable, ApplicationToNonFunction, UsageModality, InconsistentUsage, WrongOrder), litType, Scheme (Forall), prims, TypeEnv (TypeEnv))
import Control.Monad (unless, when)
import Control.Monad.Except (throwError, ExceptT, runExceptT)
import Prelude hiding (lookup)
import Types (Type ((:->)), funArgs)
import Control.Monad.Reader (asks, ReaderT (runReaderT))
import Control.Applicative ((<|>))
import Data.Maybe (fromJust)
import Data.List (groupBy, sortBy)
import Data.Ord (comparing)
import Data.Function (on)
import Data.Bifunctor (second)
import Control.Monad.State (State, modify, MonadState (get, put), evalState, gets)
import Desugar (ConstructorMap)
import Lens.Micro (set, over)
import Lens.Micro.TH ( makeLenses )

type Usage = [Name]

type LocalEnv = Map Name (Type, Modality)

type EnvDef = Map Name (Type, Modality)

data CheckState = CheckState { _orderedVars :: [Name], _localEnv :: LocalEnv }
makeLenses ''CheckState

type Check = ExceptT TypeError (ReaderT EnvDef (State CheckState))

checkUsageCount :: Modality -> Name -> Usage -> Check ()
checkUsageCount m name usage = do
    let countUsage = length $ filter (== name) usage
    let usageErr = UsageModality name m countUsage
    case m of
      Unrestricted -> pure ()
      Linear -> when (countUsage /= 1) $ throwError usageErr
      Affine -> when (countUsage > 1) $ throwError usageErr
      Relevant -> when (countUsage == 0) $ throwError usageErr
      Ordered -> do
        when (countUsage > 1) $ throwError usageErr
        vars <- gets _orderedVars
        case vars of
          var : restVars | var == name -> modify (set orderedVars restVars)
          _ -> throwError WrongOrder
        when (countUsage /= 1) $ throwError usageErr
      Zero -> when (countUsage /= 0) $ throwError usageErr

groupByFst :: (Ord a) => [(a, b)] -> [[(a, b)]]
groupByFst = groupBy ((==) `on` fst)
           . sortBy (comparing fst)

data ArgUsage = UseAny | Use0 | Use1 | UseAff | UseRel | UseOrd

argUsageToModality :: ArgUsage -> Modality
argUsageToModality UseAny = Unrestricted
argUsageToModality Use0 = Zero
argUsageToModality Use1 = Linear
argUsageToModality UseAff = Affine
argUsageToModality UseRel = Relevant
argUsageToModality UseOrd = Ordered

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
      Ordered -> do
        when (countUsage > 1) $ throwError usageErr
        vars <- gets _orderedVars
        case vars of
          var : restVars | var == name -> modify (set orderedVars restVars)
          _ -> throwError WrongOrder
        pure $ if countUsage == 1 then Use0 else UseOrd
      Zero -> do
        when (countUsage /= 0) $ throwError usageErr
        pure Use0

checkCase :: Modality -> (Pattern, Expr Scheme) -> Check ([Name], Type, [(Name, ArgUsage)])
checkCase m (pat, caseExpr)  = do
    newLocs <- case pat of
      ConstructorPattern conName args -> do
        conLookup <- asks $ lookup conName
        (conTy, conM) <- maybe (throwError $ UnboundVariable conName) pure conLookup
        unless (more m conM) $ throwError (IncorrectModalityContext conName m conM)
        pure $ zip args $ funArgs conTy
      _ -> pure []
    modify (over localEnv (`union` fromList newLocs))
    (ty, used) <- mcheck m caseExpr
    newLocEnv <- gets _localEnv
    mapM_ (\(argName, _) -> checkUsageCount (snd $ fromJust $ lookup argName newLocEnv) argName used) newLocs
    argUsage <- mapM (\(locName, (_, locM)) -> (locName,) <$> locsArgUsage locName locM used)
      $ filter (`notElem` newLocs) $ toList newLocEnv
    ordVars <- gets _orderedVars
    pure (ordVars, ty, argUsage)

mcheck :: Modality -> Expr Scheme -> Check (Type, Usage)
mcheck m (NameExpr name) = do
    defLookup <- asks $ lookup name
    locEnv <- gets _localEnv
    let lookupResult = ((, [name]) <$> lookup name locEnv) <|> ((, []) <$> defLookup)
    ((ty, varM), usage) <- maybe (throwError $ UnboundVariable name) pure lookupResult
    unless (more m varM) $ throwError (IncorrectModalityContext name m varM)
    pure (ty, usage)
mcheck m (ApplyExpr fun arg) = do
    (funTy, funUsed) <- mcheck m fun
    case funTy of
        ((am, _) :-> retTy) -> do
            (_, argUsed) <- mcheck (mult am m) arg
            pure (retTy, funUsed ++ argUsed)
        _ -> throwError ApplicationToNonFunction
mcheck _ (LambdaExpr argName (Forall _ argTy) argM expr) = do
    modify (over localEnv $ insert argName (argTy, argM))
    case argM of
      Ordered -> modify (over orderedVars $ (:) argName)
      _ -> pure ()
    (retTy, used) <- mcheck argM expr
    locEnv <- gets _localEnv
    checkUsageCount (snd $ fromJust $ lookup argName locEnv) argName used
    modify (over localEnv $ filterWithKey (\k _ -> k /= argName))
    pure ((argM, argTy) :-> retTy, filter (/= argName) used)
mcheck _ (LitExpr l) = pure (litType l, [])
mcheck m (CaseExpr matchExpr pats) = do
    (_, matchUsed) <- mcheck m matchExpr
    st <- get
    caseCheckedWithTy' <- traverse (\pe -> put st >> checkCase m pe) pats
    let (ord : orders, caseCheckedWithTy) = foldr (\(ords, t, usages) (ordAcc, restAcc) -> (ords : ordAcc, (t, usages) : restAcc)) ([], []) caseCheckedWithTy'
    unless (all (== ord) orders) $ throwError WrongOrder
    modify (set orderedVars ord)
    let ty = fst $ head caseCheckedWithTy
    let caseChecked = groupByFst $ concatMap snd caseCheckedWithTy
    newLocList <- mapM combineUsages caseChecked
    let newLoc = fromList $ second argUsageToModality <$> newLocList
    let locEnv = _localEnv st
    modify (set localEnv $ mapWithKey (\n (t, _) -> (t, fromJust $ lookup n newLoc)) locEnv)
    pure (ty, matchUsed)

runMcheck :: ConstructorMap -> [(Name, Expr Scheme, Scheme)] -> Either TypeError [(Type, Usage)]
runMcheck conMap defs =
  let envDef = fromList $ (\(n, _, Forall _ ty) -> (n, (ty, Unrestricted))) <$> defs in
  let checkDefs = mapM (mcheck Linear) ((\(_, exprTy, _) -> exprTy) <$> defs) in
  let TypeEnv primsModal = prims in
    let modalConAndPrims = Data.Map.map (\(Forall _ ty) -> (ty, Unrestricted)) $ primsModal `union` conMap in
  evalState (runReaderT (runExceptT checkDefs) (modalConAndPrims `union` envDef)) $ CheckState [] empty
