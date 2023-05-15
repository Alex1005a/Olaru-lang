{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Eval where
import Expressions
import GHC.Generics (Generic)
import Control.DeepSeq (NFData, deepseq)
import Data.Map (Map, insert, lookup, empty, fromList, union)
import Prelude hiding (lookup)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.Reader (Reader, asks, ask, runReader)
import Types (Type)

type ConstructorArity = Int

type ConstructorMap = Map Name ConstructorArity

type Env = Map Name Value
type ExprMap = Map Name (Expr Type)

data EvalError = IndalidValue | NoMatchingPatterns | UnboundName
    deriving (Show, Eq)

type Eval = ExceptT EvalError (Reader (ConstructorMap, ExprMap))

data Value
  = LitVal Literal
  | Closure (Value -> Eval Value)
  | Constructor Name [Value]
  deriving (Generic, NFData)

instance Show Value where
    show (LitVal lit) = show lit
    show (Closure _) = "closure"
    show (Constructor name vals) = name ++ "(" ++ show vals ++ ")"

instance Eq Value where
    (LitVal lit1) == (LitVal lit2) = lit1 == lit2
    (Constructor name1 vals1) == (Constructor name2 vals2) = (name1 == name2) && (vals1 == vals2)
    _ == _ = False

createConstructorClosure :: [Value] -> Int -> Name -> Value
createConstructorClosure vals 0 name = Constructor name vals
createConstructorClosure vals n name = Closure $ \v -> pure $ createConstructorClosure (vals ++ [v]) (n - 1) name

constructorClosure :: Name -> ConstructorMap -> Maybe Value
constructorClosure name constructs = do
    info <- lookup name constructs
    pure $ createConstructorClosure [] info name

integerClosure :: (Integer -> Integer -> Integer) -> Value
integerClosure f = Closure $ \v1 -> pure $ Closure $ \v2 ->
    case (v1, v2) of
        (LitVal (IntegerLiteral int1), LitVal (IntegerLiteral int2)) -> pure $ LitVal $ IntegerLiteral (f int1 int2)
        _ -> throwError IndalidValue

matchValues :: Value -> [(Pattern, Expr a)] -> ConstructorMap -> Maybe ([(Name, Value)], Expr a)
matchValues _ ((Default, expr) : _) _ = Just ([], expr)
matchValues val ((LiteralPattern lit, expr) : rest) constructs =
    if val == LitVal lit then Just ([], expr)
    else matchValues val rest constructs
matchValues val@(Constructor nameConst vals) ((ConstructorPattern namePat names, expr) : rest) constructs = do
    if nameConst == namePat then Just (zip names vals, expr)
    else matchValues val rest constructs
matchValues _ _ _ = Nothing

eval :: Expr a -> Env -> Eval Value
eval (LitExpr lit) _ = pure $ LitVal lit
eval (LambdaExpr arg _ _ expr) env = pure . Closure $ \v -> v `deepseq` eval expr (insert arg v env)
eval (ApplyExpr f x) env = do
    x_ <- eval x env
    f_ <- eval f env
    case f_ of
      (Closure f_) -> f_ x_
      _ -> throwError IndalidValue
eval (NameExpr "plus") _ = pure $ integerClosure (+)
eval (NameExpr "mult") _ = pure $ integerClosure (*)
eval (NameExpr "minus") _ = pure $ integerClosure (-)
eval (NameExpr name) env = do
    (constructs, exprs) <- ask
    case constructorClosure name constructs of
        Just con -> pure con
        Nothing -> 
            case lookup name exprs of
                Just expr -> eval expr empty
                Nothing -> maybe (throwError UnboundName) pure (lookup name env)
eval (CaseExpr expr patterns) env = do
    val <- eval expr env
    constructs <- asks fst
    case matchValues val patterns constructs of
        Just (vars, patExpr) -> eval patExpr $ fromList vars `union` env
        Nothing -> throwError NoMatchingPatterns

evalName :: Name -> ExprMap -> ConstructorMap -> Either EvalError Value
evalName name exprs constructs = do
    expr <- maybe (throwError UnboundName) pure $ lookup name exprs
    runReader (runExceptT (eval expr empty)) (constructs, exprs)