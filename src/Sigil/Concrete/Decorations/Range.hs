module Sigil.Concrete.Decorations.Range
  ( Range(..) ) where

{------------------------------------ RANGE ------------------------------------}
{- The Range decoration is designed to encapsulate source position information -}
{- for syntax highlighting and error reporting.                                -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Text.Megaparsec


newtype Range = Range { un_range :: Maybe (SourcePos, SourcePos) }
  deriving (Eq, Show, Ord)
  
-- TODO: improve ranges
instance Semigroup Range where
  (Range (Just (s, e))) <> (Range (Just (s', e'))) = Range $ Just (start s s', end e e')
    where 
      start (SourcePos p l c) (SourcePos _ l' c') = SourcePos p (min l l') (min c c')
      end (SourcePos _ l c) (SourcePos p' l' c') = SourcePos p' (max l l') (max c c')

  (Range (Just r)) <> (Range Nothing)  = Range (Just r)
  (Range Nothing)  <> (Range (Just r)) = Range (Just r)
  (Range Nothing)  <> (Range Nothing)  = Range Nothing

instance Monoid Range where
  mempty = Range Nothing
