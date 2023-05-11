{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Eval where
import Expressions
import GHC.Generics (Generic)
import Control.DeepSeq (NFData, deepseq)
import Data.Map (Map, insert, lookup, empty, fromList, union)
import Prelude hiding (lookup)
import Data.Maybe (fromJust)
import Control.Applicative ((<|>))

type ConstructorArity = Int

type ConstructorMap = Map Name ConstructorArity

type Env = Map Name Value

type ExprMap a = Map Name (Expr a)

data Value
  = LitVal Literal
  | Closure (Value -> Value)
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
createConstructorClosure vals n name = Closure $ \v -> createConstructorClosure (vals ++ [v]) (n - 1) name

constructorClosure :: Name -> ConstructorMap -> Maybe Value
constructorClosure name constructs = do
    info <- lookup name constructs
    pure $ createConstructorClosure [] info name

integerClosure :: (Integer -> Integer -> Integer) -> Value
integerClosure f = Closure $ \v1 -> Closure $ \v2 ->
    case (v1, v2) of
        (LitVal (IntegerLiteral int1), LitVal (IntegerLiteral int2)) -> LitVal $ IntegerLiteral (f int1 int2)
        _ -> error "Not two int"

matchValues :: Value -> [(Pattern, Expr a)] -> ConstructorMap -> Maybe ([(Name, Value)], Expr a)
matchValues _ ((Default, expr) : _) _ = Just ([], expr)
matchValues val ((LiteralPattern lit, expr) : rest) constructs =
    if val == LitVal lit then Just ([], expr)
    else matchValues val rest constructs
matchValues val@(Constructor nameConst vals) ((ConstructorPattern namePat names, expr) : rest) constructs = do
    if nameConst == namePat then Just (zip names vals, expr)
    else matchValues val rest constructs
matchValues _ _ _ = Nothing

eval :: Expr a -> (ExprMap a, ConstructorMap) -> Env -> Maybe Value
eval (LitExpr lit) _ _ = Just $ LitVal lit
eval (LambdaExpr arg _ _ expr) ast env = pure . Closure $ \v -> v `deepseq` fromJust $ eval expr ast (insert arg v env)
eval (ApplyExpr f x) ast env = do
    x_ <- eval x ast env
    (Closure f_) <- eval f ast env
    Just $ f_ x_
eval (NameExpr "plus") _ _ = pure $ integerClosure (+)
eval (NameExpr "mult") _ _ = pure $ integerClosure (*)
eval (NameExpr "minus") _ _ = pure $ integerClosure (-)
eval (NameExpr name) (exprs, constructs) env =
    constructorClosure name constructs
    <|> (do
    expr <- lookup name exprs
    eval expr (exprs, constructs) empty)
    <|> lookup name env
eval (CaseExpr expr patterns) (exprs, constructs) env = do
    val <- eval expr (exprs, constructs) env
    (vars, patExpr) <- matchValues val patterns constructs
    eval patExpr (exprs, constructs) (fromList vars `union` env)

evalName :: Name -> (ExprMap a, ConstructorMap) -> Maybe Value
evalName name (exprs, constructs) = do
    expr <- lookup name exprs
    eval expr (exprs, constructs) empty