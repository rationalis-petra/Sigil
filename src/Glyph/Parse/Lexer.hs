module Glyph.Parse.Lexer
  ( sc
  , symbol
  , lexeme
  , anyvar
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

symbol :: Text -> Parser Text
symbol = L.symbol sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

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
