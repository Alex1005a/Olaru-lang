{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Expressions where
import Algebra (Modality)
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)

type Name = String

data Literal
  = IntegerLiteral Integer
  | CharLiteral Char
  deriving (Eq, Show, Generic, NFData)

data Expr a
  = LambdaExpr Name a Modality (Expr a)
  | NameExpr Name
  | LitExpr Literal
  | ApplyExpr (Expr a) (Expr a)
  | CaseExpr (Expr a) [(Pattern, Expr a)]
  deriving (Eq, Show)

data Pattern
  = Default
  | LiteralPattern Literal
  | ConstructorPattern Name [Name]
  deriving (Eq, Show)
