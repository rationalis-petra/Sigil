module Sigil.Concrete.Decorations.Implicit
  ( ImplCore(..)
  , IAbsχ
  , IPrdχ
  , TyConχ
  ) where

import qualified Data.Map as Map   

import Sigil.Abstract.Syntax 
import Sigil.Abstract.Environment 
import Sigil.Abstract.AlphaEq 

data ImplCore b n χ
  = IAbsχ (IAbsχ χ) (b n (Core b n χ)) (Core b n χ) -- Implicit lambda λ [{A:𝕌} (x:A)] x
  | IPrdχ (IPrdχ χ) (b n (Core b n χ)) (Core b n χ)    -- Implicit d-prod {A:𝕌} → A
  | TyConχ (TyConχ χ) n (Core b n χ)   -- Constrains named type n  

type family IAbsχ χ
type family IPrdχ χ
type family TyConχ χ


instance (Ord n, Binding b, AlphaEq n (Core b n χ), AlphaEq n (b n (Core b n χ))) => AlphaEq n (ImplCore b n χ) where
  αequal rename v v' = case (v, v') of 
    (IAbsχ _ b e, IAbsχ _ b' e') ->
      αequal rename b b' && αequal rename' e e'
      where
        rename' = ( maybe (fst rename) (\n -> Map.insert n (name b') (fst rename)) (name b)
                  , maybe (snd rename) (\n -> Map.insert n (name b) (snd rename)) (name b'))
    (IPrdχ _ b t, IPrdχ _ b' t') ->
      αequal rename b b' && αequal rename' t t'
      where
        rename' = ( maybe (fst rename) (\n -> Map.insert n (name b') (fst rename)) (name b)
                  , maybe (snd rename) (\n -> Map.insert n (name b) (snd rename)) (name b'))
      -- TODO: this might be wrong!
    (TyConχ _ n t, TyConχ _ n' t') -> 
      case (Map.lookup n (fst rename), Map.lookup n' (snd rename)) of
        (Just (Just r), Just (Just r')) -> r == n' && r' == n && αequal rename t t'
        (Nothing, Nothing) -> n == n' && αequal rename t t'
        _ -> False
    _ -> False

instance (Eq n, Eq (IAbsχ χ), Eq (IPrdχ χ), Eq (TyConχ χ), Eq (b n (Core b n χ)), Eq (Core b n χ)) => Eq (ImplCore b n χ) where
  v == v' = case (v, v') of 
    (IAbsχ χ₁ b₁ e₁, IAbsχ χ₂ b₂ e₂) ->
      χ₁ == χ₂ && b₁ == b₂ && e₁ == e₂
    (IPrdχ χ₁ b₁ t₁, IPrdχ χ₂ b₂ t₂) ->
      χ₁ == χ₂ && b₁ == b₂ && t₁ == t₂
    (TyConχ χ₁ n₁ t₁, TyConχ χ₂ n₂ t₂) -> 
      χ₁ == χ₂ && n₁ == n₂ && t₁ == t₂
    _ -> False

