module Glyph.Parse.Combinator
  ( Parser
  , betweenM
  , many1
  , choice'
  , (<||>)
  ) where

{--------------------------------- COMBINATORS ---------------------------------}
{- This file contains extra combinators for parsing.                           -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (head, last, tail)
import Data.Vector (Vector, head, last, tail)
import Data.Text (Text)

import Text.Megaparsec hiding (runParser)

{--------------------------------- PARSER TYPE ---------------------------------}


type Parser = Parsec Text Text


{--------------------------------- COMBINATORS ---------------------------------}

  
betweenM :: Vector (Parser b) -> Parser a -> Parser [a]  
betweenM vec p = case length vec of 
  0 -> pure []
  1 -> head vec *> pure []
  2 -> between (head vec) (last vec) ((\x -> [x]) <$> p)
  _ -> (head vec) *> ((:) <$> p <*> betweenM (tail vec) p)

-- Parse many of an element (min 1) 
many1 :: Parser a -> Parser [a]
many1 p = (:) <$> p <*> many p 

-- choice with backtracking
choice' :: [Parser a] -> Parser a
choice' = choice . fmap try

infixl 3 <||>
-- <|> with backtracking
(<||>) :: Parser a -> Parser a -> Parser a
l <||> r = try l <|> try r
