{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Glyph.Parse.Lexer
  ( sc
  , scn
  , symbol
  , symboln
  , lexeme
  , lexemen
  , anyvar
  , subscript_int
  ) where

{-------------------------------- LEXING TOOLS ---------------------------------}
{- The lexer is rather complicated, as tokenization depends on two things:     -}
{- • What is currently being parsed (e.g. a definition vs an expression)       -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Data.Text (Text, pack)
import Data.Functor (($>))
import Control.Monad (void)

import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char
import Text.Megaparsec hiding (Token)

import Glyph.Parse.Combinator
import Prelude hiding (head)


sc :: ParserT m () 
sc = L.space
  (void $ char ' ' <|> char '\t')
  (L.skipLineComment "⍝")   
  (L.skipBlockComment "⋳" "⋻")

scn :: ParserT m () 
scn = L.space
  space1
  (L.skipLineComment "⍝")   
  (L.skipBlockComment "⋳" "⋻")

-- indent_block1 :: Parser a -> Parser [a]
-- indent_block1 =
--   L.indentBlock sc indented_block
--   where 
--     indented_block = do
  

lexemen :: ParserT m a -> ParserT m a
lexemen = L.lexeme scn

lexeme :: ParserT m a -> ParserT m a
lexeme = L.lexeme sc

symbol :: Text -> ParserT m Text
symbol = L.symbol sc

symboln :: Text -> ParserT m Text
symboln = L.symbol scn

subscript_int :: ParserT m Int -- TODO update to INTEGER
subscript_int = lexeme $ to_int 1 . reverse <$> many1 sub_numchar
  where
    to_int _ [] = 0
    to_int n (x:xs) = n * x + to_int (n * 10) xs

    sub_numchar = choice
      [ satisfy (== '₀') $>  0
      , satisfy (== '₁') $>  1  
      , satisfy (== '₂') $>  2  
      , satisfy (== '₃') $>  3  
      , satisfy (== '₄') $>  4  
      , satisfy (== '₅') $>  5  
      , satisfy (== '₆') $>  6  
      , satisfy (== '₇') $>  7  
      , satisfy (== '₈') $>  8  
      , satisfy (== '₉') $>  9
      ]

anyvar :: ParserT m Text  
anyvar = lexeme $ pack <$> many1 (satisfy symchar)
  where 
    symchar :: Char -> Bool
    symchar '('  = False
    symchar ')'  = False
    symchar '.'  = False
    symchar '≜'  = False
    symchar ' '  = False
    symchar '\n' = False
    symchar '\r' = False
    symchar '\t' = False
    symchar _    = True
