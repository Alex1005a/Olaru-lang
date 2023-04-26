{-# LANGUAGE TupleSections #-}
module ModalCheck where

import Expressions (Name, Expr (NameExpr, ApplyExpr, LambdaExpr, LitExpr, CaseExpr), Pattern (ConstructorPattern))
import Algebra (Modality (Unrestricted, Linear, Affine, Relevant), more, mult)
import Data.Map (Map, lookup, insert, fromList, union, toList)
import TypeCheck (TypeError (IncorrectModalityContext, UnboundVariable, ApplicationToNonFunction, UsageModality), litType)
import Control.Monad (unless, when)
import Control.Monad.Except (throwError, ExceptT)
import Prelude hiding (lookup)
import Types (Type ((:->)), funArgs)
import Control.Monad.Reader (Reader, asks)
import Control.Applicative ((<|>))

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

mcheck :: Modality -> LocalEnv -> Expr Type -> Check (Type, Usage)
mcheck m env (NameExpr name) = do
    defLookup <- asks $ lookup name
    let lookupResult = ((, [name]) <$> lookup name env) <|> ((, []) <$> defLookup)
    ((ty, varM), usage) <- throwFromMaybe (UnboundVariable name) lookupResult
    unless (more m varM) $ throwError (IncorrectModalityContext name m varM)
    pure (ty, usage)
mcheck m locEnv (ApplyExpr fun arg) = do
    (funTy, funUsed) <- mcheck m locEnv fun
    case funTy of
        ((am, _) :-> retTy) -> do
            (_, argUsed) <- mcheck (mult am m) locEnv arg
            pure (retTy, funUsed ++ argUsed)
        _ -> throwError ApplicationToNonFunction
mcheck _ locEnv (LambdaExpr argName argTy argM expr) = do
    (retTy, used) <- mcheck argM (insert argName (argTy, argM) locEnv) expr
    checkUsageCount argM argName used
    pure ((argM, argTy) :-> retTy, filter (/= argName) used)
mcheck _ _ (LitExpr l) = pure (litType l, [])
mcheck m env (CaseExpr matchExpr pats) = do
    (matchTy, matchUsed) <- mcheck m env matchExpr
    undefined
    --matchUsed ++ caseu

data ArgUsage = UseAny | Use0 | Use1 | UseAff | UseRel

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

checkCase :: Modality -> (Pattern, Expr Type) -> LocalEnv -> Check (Type, [(Name, ArgUsage)])
checkCase m (pat, caseExpr) locEnv = do
    newLocs <- case pat of
      ConstructorPattern conName args -> do
        conLookup <- asks $ lookup conName
        (conTy, conM) <- throwFromMaybe (UnboundVariable conName) conLookup
        unless (more m conM) $ throwError (IncorrectModalityContext conName m conM)
        pure $ zip args $ funArgs conTy
      _ -> pure []
    (ty, used) <- mcheck m (union locEnv $ fromList newLocs) caseExpr
    mapM_ (\(argName, (_, argM)) -> checkUsageCount argM argName used) newLocs
    argUsage <- mapM (\(locName, (_, locM)) -> (locName,) <$> locsArgUsage locName locM used) $ toList locEnv
    pure (ty, argUsage)
