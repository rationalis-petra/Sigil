module Sigil.Concrete.Parsed
  ( Parsed
  , ParsedCore
  , ParsedEntry
  , ParsedModule
  , PUnit(..)
  , pattern Core
  , pattern Uni
  , pattern Var
  , pattern Prd
  , pattern Abs
  , pattern App
  ) where

{----------------------------------- PARSED ------------------------------------}
{- The Parsed Type describes s the creation and manipulation of abstract Sigil.-}
{- terms, i.e. the core calculus. This includes:                               -}
{- • Representation of Sigil. Terms and Environments                           -}
{- • Normalization                                                             -}
{- • Substitution                                                              -}
{- • Higher Order Unification                                                  -}
{- • Type Checking & Type Inference                                            -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Data.Text

import Prettyprinter

import Sigil.Abstract.Environment
import Sigil.Abstract.Syntax
import Sigil.Abstract.AlphaEq
import Sigil.Concrete.Decorations.Range

data PUnit = PUnit

instance AlphaEq Text PUnit where   
  αequal _ PUnit PUnit = True

instance Pretty PUnit where   
  pretty PUnit = ""

data Parsed
type instance Coreχ OptBind Text Parsed = PUnit
type instance Varχ Parsed = Range
type instance Uniχ Parsed = Range
type instance Prdχ Parsed = Range
type instance Absχ Parsed = Range
type instance Appχ Parsed = Range
type instance Eqlχ Parsed = Range
type instance Dapχ Parsed = Range

type ParsedCore = Core OptBind Text Parsed

type instance Mutualχ Parsed = Range
type instance Singleχ Parsed = Range

type ParsedEntry = Entry OptBind Text Parsed

type ParsedModule = Module OptBind Text Parsed

{-# COMPLETE Core, Uni, Var, Prd, Abs, App #-}
pattern Core :: ParsedCore
pattern Core <- Coreχ _
  where Core = Coreχ PUnit
  
pattern Uni :: Range -> Integer -> ParsedCore
pattern Uni r n <- Uniχ r n
  where Uni r n = Uniχ r n

pattern Var :: Range -> Text -> ParsedCore
pattern Var r n <- Varχ r n
  where Var r n = Varχ r n

pattern Prd :: Range -> OptBind Text ParsedCore -> ParsedCore -> ParsedCore
pattern Prd r b e <- Prdχ r b e
  where Prd r b e = Prdχ r b e

pattern Abs :: Range -> OptBind Text ParsedCore -> ParsedCore -> ParsedCore
pattern Abs r b e <- Absχ r b e
  where Abs r b e = Absχ r b e

pattern App :: Range -> ParsedCore -> ParsedCore -> ParsedCore
pattern App r a b <- Appχ r a b
  where App r a b = Appχ r a b

instance HasRange ParsedCore where
  range core = case core of
    Core -> mempty
    Uni r _ -> r
    Var r _ -> r
    Prd r _ _ -> r
    Abs r _ _ -> r
    App r _ _ -> r

  
{---------------------------------- INSTANCES ----------------------------------}


instance Pretty ParsedCore where
  pretty =
    pretty_core_builder pretty_bind pretty pretty
  
instance Pretty ParsedEntry where
  pretty =
    pretty_entry_builder name pretty pretty pretty

instance Pretty ParsedModule where
  pretty =
    pretty_mod_builder pretty
