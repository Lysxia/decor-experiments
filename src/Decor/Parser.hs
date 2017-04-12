{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Decor.Parser where

import Data.Foldable
import Text.Megaparsec
import qualified Text.Megaparsec.Lexer as L

import Decor.Types hiding (DCore)
import qualified Decor.Types as DC

data Partial

type instance VarT  Partial = String
type instance BindVarT Partial = String
type instance RelT Partial = Rel
type instance DC.DCore Partial = DCore
type instance FunT  Partial = ()
type instance CVarT Partial = ()
type instance BindCVarT Partial = ()
type instance Coercion Partial = ()

type DCore = Maybe (DCore_ Partial)

type Parser = Parsec Dec String

symbol :: String -> Parser String
symbol = L.symbol space

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

parseDCore :: Parser DCore
parseDCore = do
  ts <- some parseSimpleDCore
  return (foldl1 (\t t' -> Just (App t t' Rel)) ts)

parseSimpleDCore :: Parser DCore
parseSimpleDCore =
  symbol "_" *> return Nothing <|>
  symbol "(" *> parseDCore <* symbol ")" <|>
  Just <$> asum
    [ symbol "*" *> return Star
    , parseForall
    , parseFun
    , Var <$> parseVar
    ]

parseForall :: Parser (DCore_ Partial)
parseForall = do
  v <- symbol "forall" *> parseVar
  ty <- symbol ":" *> parseDCore
  t <- symbol "." *> parseDCore
  return (Pi Rel v ty t)

parseFun :: Parser (DCore_ Partial)
parseFun = do
  v <- symbol "fun" *> parseVar
  ty <- symbol ":" *> parseDCore
  t <- symbol "->" *> parseDCore
  return (Abs Rel v ty t)

parseVar :: Parser String
parseVar = lexeme (try (some alphaNumChar))

parseDC :: String -> Either (ParseError Char Dec) DCore
parseDC = parse parseDCore ""
