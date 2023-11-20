module Sigil.Parse.Combinator
  ( Parser
  , ParserT
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
import Data.Text (Text)

import Text.Megaparsec hiding (runParser)

{--------------------------------- PARSER TYPE ---------------------------------}


type ParserT = ParsecT Text Text 
type Parser = Parsec Text Text


{--------------------------------- COMBINATORS ---------------------------------}

-- Parse many of an element (min 1) 
many1 :: (MonadParsec e s m) => m a -> m [a]
many1 p = (:) <$> p <*> many p 

thread :: (MonadParsec e s m) => (a -> m a) -> a -> m a   
thread p val = (p val >>= thread p) <||> pure val

thread1 :: (MonadParsec e s m) => (a -> m a) -> a -> m a   
thread1 p val = p val >>= thread p

-- choice with backtracking
choice' :: (MonadParsec e s m) => [m a] -> m a
choice' = choice . fmap try

infixl 3 <||>
-- <|> with backtracking
(<||>) :: (MonadParsec e s m) => m a -> m a -> m a
l <||> r = try l <|> try r
