module Sigil.Parse.Lexer
  ( sc
  , scn
  , symbol
  , lexeme
  , lparen
  , rparen
  , langle
  , rangle
  , anyvar
  , subscript_int
  , rational
  ) where

{-------------------------------- LEXING TOOLS ---------------------------------}
{- The lexer is rather complicated, as tokenization depends on two things:     -}
{- • What is currently being parsed (e.g. a definition vs an expression)       -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Data.Ratio ((%))
import Data.Text (Text)
import Data.Functor (($>))
import Control.Monad (void)

import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char
import Text.Megaparsec

import Sigil.Parse.Combinator
import Prelude hiding (head)


sc :: (MonadParsec e Text m) => m () 
sc = L.space
  (void $ char ' ' <|> char '\t')
  (L.skipLineComment "⍝")   
  (L.skipBlockComment "⋳" "⋻")

scn :: (MonadParsec e Text m) => m ()
scn = L.space
  space1
  (L.skipLineComment "⍝")   
  (L.skipBlockComment "⋳" "⋻")

lexeme :: (MonadParsec e Text m) => m a -> m a
lexeme = L.lexeme sc

symbol :: (MonadParsec e Text m) => Text -> m ()
symbol txt = void $ (string txt <* (lookAhead (satisfy (not . symchar) *> pure () <|> eof)) <* sc)

lparen :: (MonadParsec e Text m) => m ()  
lparen = void $ char '(' <* sc

rparen :: (MonadParsec e Text m) => m ()  
rparen = void $ char ')' <* sc

langle :: (MonadParsec e Text m) => m ()  
langle = void $ char '⟨' <* sc

rangle :: (MonadParsec e Text m) => m ()  
rangle = void $ char '⟩' <* sc

subscript_int :: (MonadParsec e Text m) => m Integer
subscript_int = lexeme $ to_int 1 . reverse <$> many1 sub_numchar
  where
    to_int _ [] = 0
    to_int n (x:xs) = n * x + to_int (n * 10) xs

    sub_numchar :: (MonadParsec e Text m) => m Integer
    sub_numchar = choice sn_list
    sn_list :: (MonadParsec e Text m) => [m Integer]
    sn_list = 
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

rational :: (MonadParsec e Text m) => m Rational  
rational = lexeme $ do
  int_part <- to_int 1 10 . reverse <$> many1 numchar
  next <- lookAhead (satisfy (const True))
  case next of
    '⁄' -> satisfy (const True) *> pfrac int_part
    '.' -> satisfy (const True) *> pdec int_part
    _ -> pure $ int_part % 1
  
  where
    to_int _ _ [] = 0
    to_int n b (x:xs) = n * x + to_int (n * b) b xs

    --to_dec :: Rational -> Rational -> [Integer] -> Rational
    to_dec _ _ [] = 0
    to_dec n b (x:xs) = (x % n) + to_dec (n * b) b xs

    pfrac numerator = do
      denominator <- to_int 1 10 . reverse <$> many1 numchar
      pure $ numerator % denominator

    pdec num = do
      dec <- to_dec 10 10 <$> many1 numchar
      pure $ (num % 1) + dec

    numchar :: (MonadParsec e Text m) => m Integer
    numchar = choice n_list
    n_list :: (MonadParsec e Text m) => [m Integer]
    n_list = 
      [ satisfy (== '0') $>  0
      , satisfy (== '1') $>  1  
      , satisfy (== '2') $>  2  
      , satisfy (== '3') $>  3  
      , satisfy (== '4') $>  4  
      , satisfy (== '5') $>  5  
      , satisfy (== '6') $>  6  
      , satisfy (== '7') $>  7  
      , satisfy (== '8') $>  8  
      , satisfy (== '9') $>  9
      ]


anyvar :: (MonadParsec e Text m) => m Text  
anyvar = lexeme $ takeWhile1P (Just "symbol-character") symchar

symchar :: Char -> Bool
symchar '('  = False
symchar ')'  = False
symchar '⟨'  = False
symchar '⟩'  = False
symchar '.'  = False
symchar ','  = False
symchar '≜'  = False
symchar '⮜'  = False
symchar '→'  = False
symchar '↑'  = False
symchar '↓'  = False
symchar '⎕'  = False
symchar '⍃'  = False
symchar '⍄'  = False
symchar ' '  = False
symchar '\n' = False
symchar '\r' = False
symchar '\t' = False
-- Related to formula parsing: should be changed... 
symchar '⩑'  = False
symchar '≗'  = False
symchar '⋵'  = False
symchar _    = True
