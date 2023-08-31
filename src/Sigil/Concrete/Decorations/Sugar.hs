module Sigil.Concrete.Decorations.Sugar
  ( Sugar(..)
  , Letχ
  , Whereχ ) where

{------------------------------------ SUGAR ------------------------------------}
{- This module contains the 'syntactic sugar' extension to                     -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Sigil.Abstract.Syntax

data Sugar b n χ
  = Let (Letχ χ) [b n (Core b n χ)]
  | Where (Whereχ χ) [b n (Core b n χ)]


type family Letχ χ
type family Whereχ χ
