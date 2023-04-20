{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Eval where
import Expressions
import GHC.Generics (Generic)
import Control.DeepSeq (NFData, deepseq)
import Data.Map (Map, insert, lookup, empty, fromList, union)
import Types (Type, arity)
import Prelude hiding (lookup)
import Data.Maybe (fromJust)
import Control.Applicative ((<|>))

data ConstructorInfo = ConstructorInfo
  {
    constructorType :: Type
  } deriving (Eq, Show)

constructorArity :: ConstructorInfo -> Int
constructorArity = arity . constructorType

type ConstructorMap = Map Name ConstructorInfo

data AST = AST ConstructorMap [ValueDefinition] deriving (Eq, Show)

data ValueDefinition
  = TypeAnnotation Name Type
  | NameDefinition Name Expr
  deriving (Eq, Show)

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

type Env = Map Name Value

getNameDefinition :: Name -> [ValueDefinition] -> Maybe ValueDefinition
getNameDefinition name (TypeAnnotation {} : rest) = getNameDefinition name rest
getNameDefinition name (NameDefinition nameDef expr : rest) =
    if name == nameDef then Just (NameDefinition nameDef expr)
    else getNameDefinition name rest
getNameDefinition _ _ = Nothing

createConstructorClosure :: [Value] -> Int -> Name -> Value
createConstructorClosure vals 0 name = Constructor name vals
createConstructorClosure vals n name = Closure $ \v -> createConstructorClosure (vals ++ [v]) (n - 1) name

constructorClosure :: Name -> ConstructorMap -> Maybe Value
constructorClosure name constructs = do
    info <- lookup name constructs
    pure $ createConstructorClosure [] (constructorArity info) name

integerClosure :: (Integer -> Integer -> Integer) -> Value
integerClosure f = Closure $ \v1 -> Closure $ \v2 ->
    case (v1, v2) of
        (LitVal (IntegerLiteral int1), LitVal (IntegerLiteral int2)) -> LitVal $ IntegerLiteral (f int1 int2)
        _ -> error "Not two int"

matchValues :: Value -> [(Pattern, Expr)] -> ConstructorMap -> Maybe ([(Name, Value)], Expr)
matchValues _ ((Default, expr) : rest) _ = Just ([], expr)
matchValues val ((LiteralPattern lit, expr) : rest) constructs =
    if val == LitVal lit then Just ([], expr)
    else matchValues val rest constructs
matchValues val@(Constructor nameConst vals) ((ConstructorPattern namePat names, expr) : rest) constructs = do
    if nameConst == namePat then Just (zip names vals, expr)
    else matchValues val rest constructs
matchValues _ _ _ = Nothing

eval :: Expr -> AST -> Env -> Maybe Value
eval (LitExpr lit) _ _ = Just $ LitVal lit
eval (LambdaExpr arg _ _ expr) ast env = pure . Closure $ \v -> v `deepseq` fromJust $ eval expr ast (insert arg v env)
eval (ApplyExpr f x) ast env = do
    x_ <- eval x ast env
    (Closure f_) <- eval f ast env
    Just $ f_ x_
eval (NameExpr "plus") _ _ = pure $ integerClosure (+)
eval (NameExpr "mult") _ _ = pure $ integerClosure (*)
eval (NameExpr "minus") _ _ = pure $ integerClosure (-)
eval (NameExpr name) ast@(AST constructs values) env =
    constructorClosure name constructs
    <|> (do
    (NameDefinition _ expr) <- getNameDefinition name values
    eval expr ast empty)
    <|> lookup name env
eval (CaseExpr expr patterns) ast@(AST constructs _) env = do
    val <- eval expr ast env
    (vars, patExpr) <- matchValues val patterns constructs
    eval patExpr ast (fromList vars `union` env)

evalName :: Name -> AST -> Maybe Value
evalName name ast@(AST _ values) = do
    (NameDefinition nameDef expr) <- getNameDefinition name values
    eval expr ast empty