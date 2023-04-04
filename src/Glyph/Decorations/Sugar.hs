module Glyph.Decorations.Sugar
  ( Sugar(..) ) where

{------------------------------------ SUGAR ------------------------------------}
{- This module contains the 'syntactic sugar' extension to                     -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Glyph.Abstract.Syntax

data Sugar b n χ
  = Let (Letχ χ) [b n (Core b n χ)]
  | Where (Whereχ χ) [b n (Core b n χ)]


type family Letχ  
type family Whereχ  
