module Sigil.Concrete.Decorations.Implicit
  ( ArgType(..)
  , TyCon(..)
  , TyConχ
  ) where

import qualified Data.Map as Map   

import Sigil.Abstract.Syntax 
import Sigil.Abstract.AlphaEq 

data ArgType = Implicit | Regular -- will add | Typeclass  
  deriving (Eq, Ord, Show)

data TyCon b n χ
  = TyConχ (TyConχ χ) (Core b n χ) n (Core b n χ)   -- Constrains named type n  

type family TyConχ χ

instance (Ord n, AlphaEq n (Core b n χ), AlphaEq n (b n (Core b n χ))) => AlphaEq n (TyCon b n χ) where
  αequal rename v v' = case (v, v') of 
    -- TODO: this might be wrong!
    (TyConχ _ e₁ n₁ t₁, TyConχ _ e₂ n₂ t₂) -> 
      case (Map.lookup n₁ (fst rename), Map.lookup n₂ (snd rename)) of
        (Just (Just r₁), Just (Just r₂)) -> r₁ == n₂ && r₂ == n₁ && αequal rename t₁ t₂ && αequal rename e₁ e₂
        (Nothing, Nothing) -> n₁ == n₂ && αequal rename t₁ t₂ && αequal rename e₁ e₂
        _ -> False

instance (Eq n, Eq (TyConχ χ), Eq (b n (Core b n χ)), Eq (Core b n χ)) => Eq (TyCon b n χ) where
  v == v' = case (v, v') of 
    (TyConχ χ₁ e₁ n₁ t₁, TyConχ χ₂ e₂ n₂ t₂) -> 
      χ₁ == χ₂ && e₁ == e₂ && n₁ == n₂ && t₁ == t₂

