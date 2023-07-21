{-# OPTIONS_GHC -Wno-orphans #-}
module Glint.Parse
  ( glint
  , runParser
  ) where

import Data.Text (Text, pack, unpack)

--import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec hiding (runParser)
import Prettyprinter  

import Glint.Syntax


type Parser = Parsec Text Text

-- sc :: Parser () 
-- sc = L.space space1 (fail "") (fail "")

-- lexeme :: Parser a -> Parser a
-- lexeme = L.lexeme sc

-- symbol :: Text -> Parser Text
-- symbol = L.symbol sc

glint :: Parser GlnRaw
glint = do 
  _ <- char '['
  name <- glname
  args <- pure []
  kwargs <- pure []
  _ <- char '|'
  body <- many (--(Left <$> glint) <|>
                (Right <$> non_block_str))
  _ <- char ']'
  pure $ Node name args kwargs body

non_block_str :: Parser Text
non_block_str = pack <$> many (satisfy nonspecial)

glname :: Parser Text
glname = pack <$> many (satisfy nonspecial)

nonspecial :: Char -> Bool
nonspecial v = (v /= '[') && (v /= '|') && (v /= ']')

-- non_block_str :: Parser Text
-- non_block_str = pack <$> many (satisfy (/= '['))

runParser :: Parser a -> Text -> Text -> Either (Doc ann) a
runParser p file input = case Megaparsec.runParser p (unpack file) input of
  Left err -> Left $ pretty $ errorBundlePretty err
  Right val -> Right val

instance ShowErrorComponent Text where 
  showErrorComponent = unpack
