module Sigil.Interpret.Canonical.Natives ( ) where

{-------------------------------- NATIVE TERMS ---------------------------------}
{- The term file (Sigil/Interpret/Canonical/Term.hs) implements a kind of      -}
{- normalization by evaluation (NbE). See that file for more details.          -}
{-                                                                             -}
{- What is relevant is that the normalizer has optimisations for certain types -}
{- and values. For example, the Natural number type, defined:                  -}
{-   μ ℕ ⮜ 𝕌.                                                                  -}
{-     zero ⮜ ℕ                                                                -}
{-     succ ⮜ ℕ → ℕ                                                            -}
{- is optimized so that value sof that type are converted e.g.                 -}
{-   succ (succ (succ zero)) ↝ 3 :: Integer (Haskell Integer).                 -}
{- Further, functions like _+_, _-_ etc. are optimized to their corresponding  -}
{- versions on natural numbers.                                                -}
{-                                                                             -}
{- The normalizer must be able to recognise these terms so that they can be    -}
{- converted to the more efficient implementation. This module contains        -}
{- functions to perform this function.                                         -}
{-                                                                             -}
{-------------------------------------------------------------------------------}
