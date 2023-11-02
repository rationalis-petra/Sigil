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
import Control.Monad.Reader (Reader, ReaderT)
import Data.Vector (Vector, head, last, tail)
import Data.Text (Text)

import Text.Megaparsec hiding (runParser)

{--------------------------------- PARSER TYPE ---------------------------------}


type ParserT m = ParsecT Text Text (ReaderT Pos m)
type Parser = ParsecT Text Text (Reader Pos)


{--------------------------------- COMBINATORS ---------------------------------}

  
betweenM :: Monad m => Vector (ParserT m b) -> ParserT m a -> ParserT m [a]  
betweenM vec p = case length vec of 
  0 -> pure []
  1 -> head vec *> pure []
  2 -> between (head vec) (last vec) ((: []) <$> p)
  _ -> head vec *> ((:) <$> p <*> betweenM (tail vec) p)

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
