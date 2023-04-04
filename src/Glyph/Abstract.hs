module Glyph.Abstract
  ( module Glyph.Abstract.Environment
  , module Glyph.Abstract.NameResolution
  , module Glyph.Abstract.Substitution
  , module Glyph.Abstract.Typecheck
  , module Glyph.Abstract.Syntax
  , module Glyph.Abstract.Unify
  , module Glyph.Abstract.Term ) where


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


import Glyph.Abstract.Environment
import Glyph.Abstract.NameResolution
import Glyph.Abstract.Substitution
import Glyph.Abstract.Typecheck
import Glyph.Abstract.Syntax
import Glyph.Abstract.Unify
import Glyph.Abstract.Term
