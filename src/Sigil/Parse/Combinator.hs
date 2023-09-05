module Sigil.Parse.Combinator
  ( Parser
  , ParserT
  , betweenM
  , many1
  , thread
  , thread1
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


type ParserT = ParsecT Text Text
type Parser = Parsec Text Text


{--------------------------------- COMBINATORS ---------------------------------}

  
betweenM :: Monad m => Vector (ParserT m b) -> ParserT m a -> ParserT m [a]  
betweenM vec p = case length vec of 
  0 -> pure []
  1 -> head vec *> pure []
  2 -> between (head vec) (last vec) ((: []) <$> p)
  _ -> head vec *> ((:) <$> p <*> betweenM (tail vec) p)

-- Parse many of an element (min 1) 
many1 :: ParserT m a -> ParserT m [a]
many1 p = (:) <$> p <*> many p 

thread :: Monad m => (a -> ParserT m a) -> a -> ParserT m a   
thread p val = (p val >>= thread p) <||> pure val

thread1 :: Monad m => (a -> ParserT m a) -> a -> ParserT m a   
thread1 p val = p val >>= thread p

-- choice with backtracking
choice' :: [ParserT m a] -> ParserT m a
choice' = choice . fmap try

infixl 3 <||>
-- <|> with backtracking
(<||>) :: ParserT m a -> ParserT m a -> ParserT m a
l <||> r = try l <|> try r
