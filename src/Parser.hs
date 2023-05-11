module Parser where

import Expressions (Pattern (..), Literal (CharLiteral, IntegerLiteral))
import Text.Megaparsec (Parsec, (<|>), some, many, choice, sepBy, between, sepBy1, runParser)
import Data.Void (Void)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char (string, space1, letterChar, char, upperChar)
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

constructorDefinition :: Parser ConstructorDefinition
constructorDefinition = liftA2 ConstructorDefinition constructorName (many typeArgument)

typeArgument :: Parser Type
typeArgument = namedType <|> singleType
  where
    namedType = (`CustomType` []) <$> typeName

singleType :: Parser Type
singleType = TypeVar <$> typeVar <|> PrimType <$> primType <|> parens typeExpr
  where
    primType
         =  (IntegerType <$ string "Int")
        <|> (CharType <$ string "Char")

typeExpr :: Parser Type
typeExpr = funType <|> baseType
  where
    funType = do
      argTy <- parens typeExpr
      _ <- string "->"
      retTy <- parens typeExpr
      pure $ argTy ::-> retTy
    baseType = singleType <|> customType
    customType = liftA2 CustomType typeName (many typeArgument)

startWithUpperChar :: Parser String
startWithUpperChar = do
  beginWithUpper <- some upperChar
  rest <- many letterChar
  pure $ beginWithUpper ++ rest

constructorName :: Parser ConstructorName
constructorName = startWithUpperChar

typeName :: Parser TypeName
typeName = startWithUpperChar

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

varName :: Parser Name
varName = some (letterChar <|> upperChar)

typeVar :: Parser TypeVar
typeVar = some letterChar

onePattern  :: Parser Pattern
onePattern  = choice [litPat, conPat, wildcardPat]
  where
    litPat = LiteralPattern <$> literal
    conPat = ConstructorPattern <$> constructorName <*> many varName
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

valueDefinition :: Parser ValueDefinition
valueDefinition = NameDefinition <$> varName <*> ((sc *> char '=' <* sc) *> expr)

definition :: Parser Definition
definition = fmap ValueDefinition valueDefinition <|> dataDefinition
  where
    dataDefinition =
      DataDefinition
        <$> (string "data" *> typeName)
        <*> many typeVar
        <*> (char '=' *> sepBy1 constructorDefinition (char '|'))

ast :: Parser AST
ast = sepBy definition (sc *> char ';' <* sc)

astParse :: String -> Either () AST
astParse source = first (const ()) $ runParser ast "" source