module Sigil.Abstract.AlphaEq
  ( AlphaEq(..)
  , αeq ) where


{------------------------------- Alpha Equality --------------------------------}
{- This file contans the AlphaEq typeclass (see more below), along with        -}
{- several instances of AlphaEq for various syntactic entities                 -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Control.Lens
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Functor.Classes (Eq1(..))
import Data.Foldable (foldl')

import Sigil.Abstract.Syntax
import Sigil.Abstract.Names


{-------------------------------- AlphaEq Class --------------------------------}
{- The αequal member of the AlphaEq class takes a pair of renamings (how to    -}
{- rename variables of the left-arg, and how to rename variables of the right  -}
{- arg).                                                                       -}
{-                                                                             -}
{- For example, suppose we want to figure out                                  -}
{- (λ [x] x) ≟ (λ [y] y)                                                       -}
{- Then, rename will get set to the map pair (x ↦ y, y ↦ x). When comparing    -}
{- the variables x and y, we check to see that looking up x in the first map   -}
{- equals y *and* looking up y in the second map yields x. Technically there   -}
{- is redundancy here, and I may try and improve efficiency in the future.     -}
{-                                                                             -}
{- The renaming maps may also map to nothing, i.e. they have type              -}
{- Map n (Maybe n), to cover bindings that have no name - for                  -}
{- example, if we see (λ [a] a) and (λ [_] a), the renaming will get set to    -}
{- (a → Nothing, ∅). Now, when comparing a (lhs) with a (rhs), we see that     -}
{- looking up a in the first map yields the value Nothing, which is different  -}
{- to looking up a in the second map, as it does not map to a value. Hence,    -}
{- these two terms are not equal.                                              -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


class AlphaEq n a | a -> n where
  αequal :: (Map n (Maybe n), Map n (Maybe n)) -> a -> a -> Bool

αeq :: AlphaEq n a => a -> a -> Bool
αeq = αequal (Map.empty, Map.empty)

instance (Ord n, Binding b, AlphaEq n (Core b n χ), AlphaEq n (b n (Core b n χ))) => AlphaEq n (Entry b n χ) where
  αequal rename v1 v2 = case (v1, v2) of 
    (Singleχ _ b val, Singleχ _ b' val') -> αequal rename' val val'
      where
        rename' = ( maybe (fst rename) (\n -> Map.insert n (name b') (fst rename)) (name b)
                  , maybe (snd rename) (\n -> Map.insert n (name b) (snd rename)) (name b'))

instance (Ord n, Binding b, Eq1 (Functorχ χ), Applicative (Functorχ χ), AlphaEq n (b n (Core b n χ)), AlphaEq n (Coreχ b n χ)) => AlphaEq n (Core b n χ) where
  αequal rename v v' = case (v, v') of 
    (Coreχ r, Coreχ r') ->
      αequal rename r r'
    (Uniχ _ n, Uniχ _ n') -> n == n'
    (Varχ _ n, Varχ _ n') ->
      case bimap (Map.lookup n) (Map.lookup n') rename of
        (Just (Just r), Just (Just r')) -> r == n' && r' == n
        (Nothing, Nothing) -> n == n'
        _ -> False
    (Prdχ _ b t, Prdχ _ b' t') ->
      αequal rename b b' && αequal rename' t t'
      where
        rename' = ( maybe (fst rename) (\n -> Map.insert n (name b') (fst rename)) (name b)
                  , maybe (snd rename) (\n -> Map.insert n (name b) (snd rename)) (name b'))
    (Absχ _ b e, Absχ _ b' e') ->
      αequal rename b b' && αequal rename' e e'
      where
        rename' = ( maybe (fst rename) (\n -> Map.insert n (name b') (fst rename)) (name b)
                  , maybe (snd rename) (\n -> Map.insert n (name b) (snd rename)) (name b'))
    (Appχ _ l r, Appχ _ l' r') ->
      αequal rename l l' && αequal rename r r'
    (Ctrχ _ label ty, Ctrχ _ label' ty') -> label == label' && liftEq (αequal rename) ty ty'
    (Indχ _ name fsort ctors, Indχ _ name' fsort' ctors') ->
      liftEq (αequal rename) fsort fsort'
      && foldl' (&&) True (zipWith (\(_, v) (_, v') -> αequal rename' v v') ctors ctors')
      where 
        rename' = ( Map.insert name (Just name') (fst rename)
                  , Map.insert name' (Just name) (snd rename))
    -- TODO: Rec
    (Eqlχ _ tel ty v1 v2, Eqlχ _ tel' ty' v1' v2') ->
      let (tel_eq, rename') = αequal_tel rename tel tel'
      in tel_eq && αequal rename' ty ty' && αequal rename' v1 v1' && αequal rename' v2 v2'

    (ETCχ _ val, ETCχ _ val') -> αequal rename val val'
    (CTEχ _ val, CTEχ _ val') -> αequal rename val val'
  
    (Dapχ _ tel val, Dapχ _ tel' val') ->
      let (tel_eq, rename') = αequal_tel rename tel tel'
      in tel_eq && αequal rename' val val'
    (TrLχ _ tel ty val, TrLχ _ tel' ty' val') ->
      let (tel_eq, rename') = αequal_tel rename tel tel'
      in tel_eq && αequal rename' ty ty' && αequal rename' val val'
    (TrRχ _ tel ty val, TrRχ _ tel' ty' val') ->
      let (tel_eq, rename') = αequal_tel rename tel tel'
      in tel_eq && αequal rename' ty ty' && αequal rename' val val'
    (LfLχ _ tel ty val, LfLχ _ tel' ty' val') ->
      let (tel_eq, rename') = αequal_tel rename tel tel'
      in tel_eq && αequal rename' ty ty' && αequal rename' val val'
    (LfRχ _ tel ty val, LfRχ _ tel' ty' val') ->
      let (tel_eq, rename') = αequal_tel rename tel tel'
      in tel_eq && αequal rename' ty ty' && αequal rename' val val'

    (_, _) -> False
    where
      αequal_tel rename [] [] = (True, rename)
      αequal_tel rename ((bind, val) : tel) ((bind', val') : tel') =
        let rename' =
              ( maybe (fst rename) (\n -> Map.insert n (name bind') (fst rename)) (name bind)
              , maybe (snd rename) (\n -> Map.insert n (name bind) (snd rename)) (name bind'))
        in if αequal rename bind bind' && αequal rename val val' then
             αequal_tel rename' tel tel'
           else
             (False, rename)
      αequal_tel rename _ _   = (False, rename)
    
instance (Ord n, Binding b, AlphaEq n (Core b n χ)) => AlphaEq n (b n (Core b n χ)) where
  αequal rename b b' = case (tipe b, tipe b') of 
    (Just ty, Just ty') -> αequal rename' ty ty'
      where
        rename' = ( maybe (fst rename) (\n -> Map.insert n (name b') (fst rename)) (name b)
                  , maybe (snd rename) (\n -> Map.insert n (name b) (snd rename)) (name b'))
    (Nothing, Nothing) -> True
    _ -> False

instance (Ord n, Binding b, AlphaEq n (Core b n χ)) => AlphaEq n (b n (Core b n χ, Core b n χ, Core b n χ)) where
  αequal rename b b' = case (tipe b, tipe b') of 
    (Just (ty, v1, v2), Just (ty', v1', v2')) ->
      αequal rename' ty ty' && αequal rename' v1 v1' && αequal rename' v2 v2'
      where
        rename' = ( maybe (fst rename) (\n -> Map.insert n (name b') (fst rename)) (name b)
                  , maybe (snd rename) (\n -> Map.insert n (name b) (snd rename)) (name b'))
    (Nothing, Nothing) -> True
    _ -> False

instance (Ord n, Binding b, Eq1 (Functorχ χ), Applicative (Functorχ χ),
          AlphaEq n (b n (Core b n χ)), AlphaEq n (Coreχ b n χ))
    => AlphaEq n (Module b n χ) where
  αequal rename m m' = 
    (m^.module_header == m'^.module_header) &&
    (m^.module_exports == m'^.module_exports) &&
    (m^.module_imports == m'^.module_imports) &&
    go rename (m^.module_entries) (m'^.module_entries)
    where
      go rename (d:ds) (d':ds')= 
        αequal rename d d' && go rename' ds ds'
        where
          -- TODO: INCORRECT BEHAVIOUR
          rename' = rename 
      go _ [] [] = True
      go _ _ _ = False


instance AlphaEq Name () where
  αequal _ _ _ = True
