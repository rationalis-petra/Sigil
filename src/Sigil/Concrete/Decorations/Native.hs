module Sigil.Concrete.Decorations.Native
  ( NativeType0 (..)
  , NmNative (..)
  , NeuNative (..)
  , Native (..)
  ) where

import Prettyprinter

import Sigil.Abstract.AlphaEq


{----------------------------------- NATIVE ------------------------------------}
{- The Native decoration is designed to encapsulate types which have a much    -}
{- more efficient 'native' representation, e.g. naturals, integers, etc.       -}
{- It also encapsulates functions which operate on these types, e.g. +, -, ... -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

data NativeType0 = NatTy
  deriving (Eq, Ord, Show)

data NmNative a
  = NativeType0 NativeType0
  | NativeNat Integer
  deriving (Eq, Ord, Show)

data NeuNative a
  = NeuNatSuccN Integer a -- 0 + a, 1 + a, 2 + a, 3 + a, ...
  deriving (Eq, Ord, Show)

data Native a
  = NmNative (NmNative a)
  | NeuNative (NeuNative a)
  deriving (Eq, Ord, Show)

instance Pretty a => Pretty (Native a) where
  pretty = \case
    NmNative n -> pretty n
    NeuNative n -> pretty n

instance Pretty a => Pretty (NmNative a) where
  pretty = \case
    NativeType0 ty -> pretty ty
    NativeNat n -> "#" <> pretty n

instance Pretty NativeType0 where
  pretty = \case
    NatTy -> "#ℕ"

instance Pretty a => Pretty (NeuNative a) where
  pretty = \case
    NeuNatSuccN pow val -> "#succ^" <> pretty pow <+> pretty val


instance AlphaEq n a => AlphaEq n (Native a) where
  αequal rename = curry $ \case
    (NmNative n₁, NmNative n₂) -> αequal rename n₁ n₂
    (NeuNative n₁, NeuNative n₂) -> αequal rename n₁ n₂
    _ -> False

instance AlphaEq n a => AlphaEq n (NmNative a) where
  αequal _ = curry $ \case
    (NativeType0 t₁, NativeType0 t₂) -> t₁ == t₂
    (NativeNat n₁, NativeNat n₂) -> n₁ == n₂
    _ -> False

instance AlphaEq n a => AlphaEq n (NeuNative a) where
  αequal rename = curry $ \case
    (NeuNatSuccN n₁ a₁, NeuNatSuccN n₂ a₂) -> n₁ == n₂ && αequal rename a₁ a₂
