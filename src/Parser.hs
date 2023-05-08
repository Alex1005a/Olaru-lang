module Parser where

import Expressions (Pattern (..), Literal (CharLiteral, IntegerLiteral))
import Types (Type)
import Text.Megaparsec (Parsec, (<|>), empty, some, many, choice, sepBy, between, runParser)
import Data.Void (Void)
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Char (isSpace, isLower)
import Control.Monad (void)
import Text.Megaparsec.Char (string, space1, alphaNumChar, letterChar, char)
import qualified Text.Megaparsec.Error
import Data.Bifunctor (first)

type Parser = Parsec Void String

type ValName = String

type TypeVar = String

type TypeName = String

type ConstructorName = String

type Name = String

newtype AST = AST [Definition] deriving (Eq, Show)

data Definition
  = ValueDefinition ValueDefinition
  | DataDefinition TypeName [TypeVar] [ConstructorDefinition]
  deriving (Eq, Show)

data ConstructorDefinition = ConstructorDefinition ConstructorName [Type] deriving (Eq, Show)

data ValueDefinition = NameDefinition ValName Expr
  deriving (Eq, Show)

data Expr
  = LambdaExpr [ValName] Expr
  | NameExpr Name
  | LitExpr Literal
  | ApplyExpr Expr [Expr]
  | CaseExpr Expr [(Pattern, Expr)]
  deriving (Eq, Show)

literal :: Parser Literal
literal = intLit <|> charLit
  where
    intLit = IntegerLiteral <$> L.decimal

    charLit = CharLiteral <$> apostrophed L.charLiteral

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"

varChar :: Parser Char
varChar = alphaNumChar <|> char '_'

varName :: Parser Name
varName = some letterChar--(:) <$> letterChar <*> many varChar

onePattern  :: Parser Pattern
onePattern  = choice [litPat, conPat, wildcardPat]
  where
    litPat = LiteralPattern <$> literal
    conPat = ConstructorPattern <$> varName <*> many varName
    wildcardPat = Default <$ char '_'

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

braces :: Parser a -> Parser a
braces = between (char '{') (char '}')

apostrophed :: Parser a -> Parser a
apostrophed = between (char '\'') (char '\'')

expr :: Parser Expr
expr = choice [lambdaExpr, appExpr, caseExpr]
  where
    lambdaExpr =
      LambdaExpr
        <$> (char '\\' *> some (sc *> varName <* sc) <* sc <* string "->" <* sc)
        <*> expr
    caseExpr =
      CaseExpr
        <$> (string "case" *> sc *> expr <* string "of" <* sc)
        <*> braces (sepBy ((,) <$> onePattern <* sc <* string "->" <* sc <*> expr) (char ';' <* sc))

appExpr :: Parser Expr
appExpr = do
  exprs <- some (sc *> factor <* sc)
  pure $ case exprs of 
    [e] -> e
    e : es -> ApplyExpr e es
    [] -> error "empty list in appExpr"

factor :: Parser Expr
factor = littExpr <|> nameExpr <|> parens expr
  where
    littExpr = LitExpr <$> literal
    nameExpr = NameExpr <$> varName
