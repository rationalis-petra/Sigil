module Glyph.Abstract
  ( module Glyph.Abstract.Syntax
  , module Glyph.Abstract.Environment
  --, module Glyph.Abstract.Constraints
  ) where


{---------------------------------- ABSTRACT -----------------------------------}
{- The Abstract Module handles the creation and manipulation of abstract glyph -}
{- terms, i.e. the core calculus. This includes:                               -}
{- • Representation of Glyph Terms and Environments                            -}
{- • Normalization                                                             -}
{- • Substitution                                                              -}
{- • Higher Order Unification                                                  -}
{- • Type Checking & Type Inference                                            -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment
--import Glyph.Abstract.Constraints
