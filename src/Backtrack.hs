module Backtrack
  ( Backtrack
  , run_backtrack ) where


{------------------------------ BACKTRACKING MONAD -----------------------------}
{- The backtracking monad represents computations which may:                   -}
{- • Fail                                                                      -}
{- • Succeed                                                                   -}
{- • Branch, in which case the left computation will first attempt to execute  -}
{-   if this computation succeeds, then the whole computation succeeds. If not -}
{-   then the result of the computation is the result of the right branch.     -}
{-                                                                             -}
{- The backtracking datatype/monad does not expose its' internals, as it is    -}
{- perfectly usable as an Alternative/MonadPlus/MonadError with a single       -}
{- run_backtrack function exposed.                                             -}
{-------------------------------------------------------------------------------}


import Control.Applicative
import Control.Monad
import Control.Monad.Except (MonadError, throwError, catchError)


{-------------------------- BACKTRACKING COMPUTATION ---------------------------}


data Backtrack e a  
  = Backtrack e a :<|>: Backtrack e a
  | Fail e
  | Success a


{---------------------------------- INSTANCES ----------------------------------}


instance Functor (Backtrack e) where
  fmap f b = case b of 
    l :<|>: r -> fmap f l :<|>: fmap f r
    Success v -> Success $ f v
    Fail text -> Fail text

instance Applicative (Backtrack e) where
  pure = Success

  mf <*> ma = case mf of 
    l :<|>: r -> (l <*> ma) :<|>: (r <*> ma)
    Success f -> f <$> ma
    Fail err  -> Fail err

instance Monad (Backtrack e) where
  m >>= f = case m of
    l :<|>: r -> (l >>= f) :<|>: (r >>= f)
    Success v -> f v
    Fail err  -> Fail err

instance Monoid e => Alternative (Backtrack e) where  
  empty = Fail mempty
  l <|> r = l :<|>: r

instance Monoid e => MonadPlus (Backtrack e) where
  mzero = Fail mempty
  mplus l r = l :<|>: r

instance MonadError e (Backtrack e) where
  throwError = Fail
  catchError m catch = case run_backtrack m of
    Left s -> catch s
    Right a -> Success a
 

{----------------------------------- RUNNING -----------------------------------}

  
run_backtrack :: Backtrack e a -> Either e a 
run_backtrack m = search m
  where
    -- Perform left-biased depth-first search for a Successful computation.
    search (l :<|>: r) = case search l of
      Right v -> Right v
      Left _ -> search r
    search (Success v) = Right v
    search (Fail e) = Left e

