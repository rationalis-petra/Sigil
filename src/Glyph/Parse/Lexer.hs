module Glyph.Parse.Lexer
  ( sc
  , symbol
  , lexeme
  , anyvar
  , subscript_int
  ) where


{-------------------------------- LEXING TOOLS ---------------------------------}


import Data.Text (Text, pack)

import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char
import Text.Megaparsec

import Glyph.Parse.Combinator

sc :: Parser () 
sc = L.space
  space1
  (L.skipLineComment ";;")
  (L.skipBlockComment "(;;" ";;)")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

subscript_int :: Parser Int -- TODO update to INTEGER
subscript_int = lexeme $ to_int 1 . reverse <$> many1 sub_numchar
  where
    to_int _ [] = 0
    to_int n (x:xs) = n * x + to_int (n * 10) xs

    sub_numchar = choice
      [ satisfy (== '₀') *> pure 0
      , satisfy (== '₁') *> pure 1  
      , satisfy (== '₂') *> pure 2  
      , satisfy (== '₃') *> pure 3  
      , satisfy (== '₄') *> pure 4  
      , satisfy (== '₅') *> pure 5  
      , satisfy (== '₆') *> pure 6  
      , satisfy (== '₇') *> pure 7  
      , satisfy (== '₈') *> pure 8  
      , satisfy (== '₉') *> pure 9
      ]

anyvar :: Parser Text  
anyvar = lexeme $ pack <$> (many1 (satisfy symchar))
  where 
    symchar :: Char -> Bool
    symchar '('  = False
    symchar ')'  = False
    symchar '['  = False
    symchar ']'  = False
    symchar '≜'  = False
    symchar ' '  = False
    symchar '\n' = False
    symchar '\r' = False
    symchar '\t' = False
    symchar _    = True

-- data Token = Inc | Nil | Dec | Name Text

-- lexer :: Parser [Token]
