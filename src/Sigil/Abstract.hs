module Sigil.Abstract
  ( module Sigil.Abstract.Syntax
  , module Sigil.Abstract.Environment
  --, module Sigil.Abstract.Constraints
  ) where


{---------------------------------- ABSTRACT -----------------------------------}
{- The Abstract Module handles the creation and manipulation of abstract Sigil. -}
{- terms, i.e. the core calculus. This includes:                               -}
{- • Representation of Sigil. Terms and Environments                            -}
{- • Normalization                                                             -}
{- • Substitution                                                              -}
{- • Higher Order Unification                                                  -}
{- • Type Checking & Type Inference                                            -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
--import Sigil.Abstract.Constraints
