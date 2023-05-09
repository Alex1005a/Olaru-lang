module Parser where

import Expressions (Pattern (..), Literal (CharLiteral, IntegerLiteral))
import Types (Type)
import Text.Megaparsec (Parsec, (<|>), some, many, choice, sepBy, between)
import Data.Void (Void)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char (string, space1, alphaNumChar, letterChar, char)

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

data ValueDefinition = NameDefinition ValName SugarExpr
  deriving (Eq, Show)

data SugarExpr
  = LambdaExpr [ValName] SugarExpr
  | NameExpr Name
  | LitExpr Literal
  | ApplyExpr SugarExpr [SugarExpr]
  | CaseExpr SugarExpr [(Pattern, SugarExpr)]
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
varName = some letterChar

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

expr :: Parser SugarExpr
expr = choice [lambdaExpr, appExpr, caseExpr]

lambdaExpr :: Parser SugarExpr
lambdaExpr =
  LambdaExpr
    <$> (char '\\' *> some (sc *> varName <* sc) <* sc <* string "->" <* sc)
    <*> expr

caseExpr :: Parser SugarExpr
caseExpr =
  CaseExpr
    <$> (string "case" *> sc *> expr <* string "of" <* sc)
    <*> braces (sepBy ((,) <$> onePattern <* sc <* string "->" <* sc <*> expr) (char ';' <* sc))

appExpr :: Parser SugarExpr
appExpr = do
  exprs <- some (sc *> factor <* sc)
  pure $ case exprs of 
    [e] -> e
    e : es -> ApplyExpr e es
    [] -> error "empty list in appExpr"

factor :: Parser SugarExpr
factor = littExpr <|> nameExpr <|> parens expr
  where
    littExpr = LitExpr <$> literal
    nameExpr = NameExpr <$> varName
