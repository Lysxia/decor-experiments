{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Decor.Parser where

import Data.Char (isUpper)
import Data.Foldable
import Prelude hiding (showString, showParen)
import Text.Megaparsec
import qualified Text.Megaparsec.Lexer as L
import Text.PrettyPrint hiding (space)

import Decor.Types

type Parser = Parsec Dec String

symbol :: String -> Parser String
symbol = L.symbol space

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

parseDCore :: Parser DCoreP
parseDCore = do
  ts <- some parseSimpleDCore
  return (foldl1 (\t t' -> Just (App t t' Rel)) ts)

parseSimpleDCore :: Parser DCoreP
parseSimpleDCore =
  symbol "_" *> return Nothing <|>
  symbol "(" *> parseDCore <* symbol ")" <|>
  Just <$> asum
    [ symbol "*" *> return Star
    , parseForall
    , parseFun
    , funOrVar <$> parseVar
    ]

parseForall :: Parser (DCore_ Partial)
parseForall = do
  v <- symbol "forall" *> parseVar
  ty <- symbol ":" *> parseDCore
  t <- symbol "->" *> parseDCore
  return (Pi Rel v ty t)

parseFun :: Parser (DCore_ Partial)
parseFun = do
  v <- symbol "fun" *> parseVar
  ty <- symbol ":" *> parseDCore
  t <- symbol "." *> parseDCore
  return (Abs Rel v ty t)

funOrVar :: String -> DCore_ Partial
funOrVar s | isUpper (head s) = Fun s
funOrVar s = Var s

parseVar :: Parser String
parseVar = lexeme (try (some alphaNumChar))

parseDC :: String -> Either (ParseError Char Dec) DCoreP
parseDC = parse parseDCore ""

type Printer = Int -> Doc

showString :: String -> Printer
showString s = \_ -> text s

showDCore :: DCoreP -> Printer
showDCore Nothing = showString "_"
showDCore (Just t) = showDCore_ t

showDCore_ :: DCore_ Partial -> Printer
showDCore_ t = case t of
  Star -> showString "*"
  Var v -> showString v
  Fun f -> showString f
  Pi _ v tyA tyB -> showPrec 0 $ \n ->
    sep
      [ hsep
          [ text "Π"
          , text v
          , text ":"
          , resetPrec 1 (showDCore tyA) n
          , text "->"
          ]
      , nest 2 $ showDCore tyB n
      ]
  Abs _ v tyA b -> showPrec 0 $ \n ->
    sep
      [ hsep
          [ text "λ"
          , text v
          , text ":"
          , resetPrec 1 (showDCore tyA) n
          , text "."
          ]
      , nest 2 $ showDCore b n
      ]
  App b a _ -> showPrec 10 $ \n ->
    sep
      [ resetPrec 10 (showDCore b) n
      , resetPrec 11 (showDCore a) n
      ]

showParen :: Printer -> Printer
showParen p = \n -> parens (p n)

showPrec :: Int -> Printer -> Printer
showPrec n p = \n' -> if n' > n then showParen p n else p n'

resetPrec :: Int -> Printer -> Printer
resetPrec n p = \_ -> p n
