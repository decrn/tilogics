{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Parser where

import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Text.Parsec.String (Parser)

import Infer

lambdabooldef :: P.LanguageDef st
lambdabooldef =
  haskellDef
  { P.reservedOpNames =
    ["->",".",":","=","\\"]
  , P.reservedNames   =
    ["bool"
    ,"else"
    ,"false"
    ,"if"
    ,"in"
    ,"let"
    ,"then"
    ,"true"
    ]
  }

lexer       = P.makeTokenParser lambdabooldef
parens      = P.parens lexer
braces      = P.braces lexer
identifier  = P.identifier lexer
reserved    = P.reserved lexer
reservedOp  = P.reservedOp lexer
whiteSpace  = P.whiteSpace lexer

-- Desugar let expressions into lambdas
elet :: String -> Exp -> Exp -> Exp
elet x e1 e2 = App (Absu x e2) e1

primTy :: Parser Ty
primTy = parens ty <|> Bool0 <$ reserved "bool"

ty :: Parser Ty
ty = chainr1 primTy (Func0 <$ reservedOp "->")

varExpr :: Parser Exp
varExpr = Var <$> identifier

boolLitExpr :: Parser Exp
boolLitExpr =
  Infer.True  <$ reserved "true" <|>
  Infer.False <$ reserved "false"

ifteExpr :: Parser Exp
ifteExpr =
  Ifte
  <$  reserved "if"
  <*> expr
  <*  reserved "then"
  <*> expr
  <*  reserved "else"
  <*> expr

lambdaExpr :: Parser Exp
lambdaExpr = do
  reservedOp "\\"
  x <- identifier
  (Absu x
   <$ reservedOp "."
   <*> expr
   <|>
   Abst x
   <$ reservedOp ":"
   <*> ty
   <*  reservedOp "."
   <*> expr)

letExpr :: Parser Exp
letExpr =
  elet
  <$  reserved "let"
  <*> identifier
  <*  reservedOp "="
  <*> expr
  <*  reserved "in"
  <*> expr

expr :: Parser Exp
expr = foldl1 App <$> many1 primExpr

primExpr :: Parser Exp
primExpr =
  parens expr
  <|> varExpr
  <|> boolLitExpr
  <|> ifteExpr
  <|> letExpr
  <|> lambdaExpr

parse :: String -> Either ParseError Exp
parse = Text.Parsec.parse (whiteSpace >> expr) "<stdin>"
