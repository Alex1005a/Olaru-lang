module Parser where

import Expressions (Pattern (..), Literal (CharLiteral, IntegerLiteral))
import Text.Megaparsec (Parsec, (<|>), some, many, choice, sepBy, between, sepBy1, runParser, MonadParsec (eof, try))
import Data.Void (Void)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char (space1, letterChar, char, upperChar)
import Types (PrimType (CharType, IntegerType))
import Control.Applicative (liftA2)
import Data.Bifunctor (first)

type Parser = Parsec Void String

type ValName = String

type TypeVar = String

type TypeName = String

type ConstructorName = String

type Name = String

type AST = [Definition]

data Definition
  = ValueDefinition ValueDefinition
  | DataDefinition TypeName [TypeVar] [ConstructorDefinition]
  deriving (Eq, Show)

infixr 2 ::->

data Type
    = Type ::-> Type
    | PrimType PrimType
    | CustomType TypeName [Type]
    | TypeVar TypeVar
    deriving (Eq, Show, Ord)

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

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

constructorDefinition :: Parser ConstructorDefinition
constructorDefinition = ConstructorDefinition <$> lexeme constructorName <*> many (lexeme typeArgument)

typeArgument :: Parser Type
typeArgument = try singleType <|> namedType
  where
    namedType = (`CustomType` []) <$> typeName

singleType :: Parser Type
singleType = parens typeExpr <|> TypeVar <$> typeVar <|> PrimType <$> primType
  where
    primType
         =  (IntegerType <$ symbol "Int")
        <|> (CharType <$ symbol "Char")

typeExpr :: Parser Type
typeExpr = funType <|> baseType
  where
    funType = do
      argTy <- parens $ lexeme typeExpr
      _ <- symbol "->"
      retTy <- parens $ lexeme typeExpr
      pure $ argTy ::-> retTy
    baseType = customType <|> singleType
    customType = liftA2 CustomType typeName (many $ lexeme typeArgument)

startWithUpperChar :: Parser String
startWithUpperChar = do
  beginWithUpper <- some upperChar
  rest <- many letterChar
  pure $ beginWithUpper ++ rest

constructorName :: Parser ConstructorName
constructorName = lexeme startWithUpperChar

typeName :: Parser TypeName
typeName = lexeme startWithUpperChar

literal :: Parser Literal
literal = lexeme $ intLit <|> charLit
  where
    intLit = IntegerLiteral <$> L.decimal
    charLit = CharLiteral <$> apostrophed L.charLiteral

varName :: Parser Name
varName = lexeme $ some (letterChar <|> upperChar)

typeVar :: Parser TypeVar
typeVar = lexeme $ some letterChar

onePattern  :: Parser Pattern
onePattern  = choice [litPat, conPat, wildcardPat]
  where
    litPat = LiteralPattern <$> lexeme literal
    conPat = ConstructorPattern <$> constructorName <*> many (lexeme varName)
    wildcardPat = Default <$ char '_'

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

apostrophed :: Parser a -> Parser a
apostrophed = between (symbol "\'") (symbol "\'")

expr :: Parser SugarExpr
expr = choice [caseExpr, lambdaExpr, appExpr]

lambdaExpr :: Parser SugarExpr
lambdaExpr =
  LambdaExpr
    <$> (symbol "\\" *> lexeme (some varName) <* symbol "->")
    <*> expr

caseExpr :: Parser SugarExpr
caseExpr =
  CaseExpr
    <$> (symbol "case" *> parens expr <* symbol "of")
    <*> braces (sepBy1 ((,) <$> onePattern <* symbol "->" <*> expr) (symbol ";"))

appExpr :: Parser SugarExpr
appExpr = do
  exprs <- some (lexeme factor)
  pure $ case exprs of
    [e] -> e
    e : es -> ApplyExpr e es
    [] -> error "empty list in appExpr"

factor :: Parser SugarExpr
factor = littExpr <|> nameExpr <|> parens expr
  where
    littExpr = LitExpr <$> literal
    nameExpr = NameExpr <$> varName

valueDefinition :: Parser ValueDefinition
valueDefinition = NameDefinition <$> lexeme varName <*> (symbol "=" *> expr)

definition :: Parser Definition
definition = dataDefinition <|> fmap ValueDefinition valueDefinition
  where
    dataDefinition =
      DataDefinition
        <$> (symbol "data" *> lexeme typeName)
        <*> many typeVar
        <*> (symbol "=" *> sepBy1 constructorDefinition (symbol "|"))

ast :: Parser AST
ast = sepBy definition (symbol ";")

astParse :: String -> Either () AST
astParse source = first (const ()) $ runParser (ast <* eof) "" source