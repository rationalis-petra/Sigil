module Sigil.Concrete.PreMix
  ( PreMix
  , PreMixCore
  , PreMixEntry
  , PreMixModule
  , pattern Mix
  , pattern Uni
  , pattern Var
  , pattern Prd
  , pattern Abs
  , pattern App
  ) where

{------------------------------------ READ -------------------------------------}
{- The PreMix type describes the syntax after the langauge-level structure has   -}
{- been parsed, i.e. lambdas, structures etc. However, it occurs before        -}
{- mixfix operators have been parsed, i.e. all 'mixfix' expressions are just   -}
{- lists of tokens.                                                            -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Data.Text

import Prettyprinter

import Sigil.Abstract.Environment
import Sigil.Abstract.Syntax
--import Sigil.Abstract.AlphaEq
import Sigil.Concrete.Decorations.Range

data PreMix
type PreMixCore = Core OptBind Text PreMix
type PreMixEntry = Entry OptBind Text PreMix
type PreMixModule = Module OptBind Text PreMix

type instance Coreχ OptBind Text PreMix = (Range, [(Either (Range, Text) PreMixCore)])
type instance Varχ PreMix = Range
type instance Uniχ PreMix = Range
type instance Prdχ PreMix = Range
type instance Absχ PreMix = Range
type instance Appχ PreMix = Range

type instance Mutualχ PreMix = Range
type instance Singleχ PreMix = Range


{-# COMPLETE Mix, Uni, Var, Prd, Abs, App #-}
pattern Mix :: Range -> [(Either (Range, Text) PreMixCore)] -> PreMixCore
pattern Mix r l <- Coreχ (r, l)
  where Mix r l = Coreχ (r, l)
  
pattern Uni :: Range -> Int -> PreMixCore
pattern Uni r n <- Uniχ r n
  where Uni r n = Uniχ r n

pattern Var :: Range -> Text -> PreMixCore
pattern Var r n <- Varχ r n
  where Var r n = Varχ r n

pattern Prd :: Range -> OptBind Text PreMixCore -> PreMixCore -> PreMixCore
pattern Prd r b e <- Prdχ r b e
  where Prd r b e = Prdχ r b e

pattern Abs :: Range -> OptBind Text PreMixCore -> PreMixCore -> PreMixCore
pattern Abs r b e <- Absχ r b e
  where Abs r b e = Absχ r b e

pattern App :: Range -> PreMixCore -> PreMixCore -> PreMixCore
pattern App r a b <- Appχ r a b
  where App r a b = Appχ r a b

instance HasRange PreMixCore where
  range core = case core of
    Mix r _ -> r
    Uni r _ -> r
    Var r _ -> r
    Prd r _ _ -> r
    Abs r _ _ -> r
    App r _ _ -> r

  
{---------------------------------- INSTANCES ----------------------------------}


instance Pretty PreMixCore where
  pretty =
    pretty_core_builder pretty pretty pretty_mix

    where pretty_mix (_, l) = "[" <> pretty_contents l <> "]"
          pretty_contents [] = ""
          pretty_contents [x] = either (pretty . snd) pretty x
          pretty_contents (x:xs) = either (pretty . snd) pretty x <> "," <+> pretty_contents xs
  
instance Pretty PreMixEntry where
  pretty =
    pretty_entry_builder name pretty pretty pretty

instance Pretty PreMixModule where
  pretty =
    pretty_mod_builder pretty
