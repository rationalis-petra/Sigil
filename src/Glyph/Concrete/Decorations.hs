module Glyph.Concrete.Decorations () where

{---------------------------------- CONCRETE -----------------------------------}
{- The Concrete module stands in contrast to the Abstract module - while       -}
{- the abstract module contains definitions and functions operating over an    -}
{- abstracted syntax - most notably there is the 'extensibility' parameter χ.  -}
{-                                                                             -}
{- The concrete module will provide various instances for χ, specializing the  -}
{- tree for, e.g. Parsing/Evaluating/Typechecking etc.                         -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------}
{- Importantly, we want these concretions to be compositional, i.e. I can      -}
{- take the range specialization, which annotates trees with source locations  -}
{- and combine it with the literal specialization, which provides int literals -}
{- to obtain the parsing specialization.                                       -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


{-------------------------------------------------------------------------------}
{- Architecture, i.e. how to combine??                                         -}
{- We want some kind of type-level algebra?                                    -}
{- Use type classes to encapsulate                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

