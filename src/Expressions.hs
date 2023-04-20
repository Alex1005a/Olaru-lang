{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Expressions where
import Algebra (Modality)
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Types (Type)

type Name = String

data Literal
  = IntegerLiteral Integer
  | CharLiteral Char
  deriving (Eq, Show, Generic, NFData)

data Expr
  = LambdaExpr Name Type Modality Expr
  | NameExpr Name
  | LitExpr Literal
  | ApplyExpr Expr Expr
  | CaseExpr Expr [(Pattern, Expr)]
  deriving (Eq, Show)

data Pattern
  = Default
  | LiteralPattern Literal
  | ConstructorPattern Name [Name]
  deriving (Eq, Show)