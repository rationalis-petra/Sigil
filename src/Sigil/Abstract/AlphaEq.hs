module Sigil.Abstract.AlphaEq
  ( AlphaEq(..)
  , αeq ) where


{------------------------------- Alpha Equality --------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Control.Lens
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (foldl')

import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment


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

    (Mutualχ _ terms, Mutualχ _ terms') -> defs_eq rename' terms terms'
      where
        rename' =
          foldl' (\r ((n,_,_), (n',_,_)) ->
                    bimap (Map.insert n (Just n')) (Map.insert n' (Just n)) r)
                        rename
                        (zip terms terms')

        defs_eq _ [] [] = True
        defs_eq r ((_,ty,val) : terms) ((_,ty',val') : terms') =
          αequal r ty ty' && αequal r val val' && defs_eq r terms terms'
        defs_eq _ _ _ = False
          
    (_, _) -> False

instance (Ord n, Binding b, AlphaEq n (b n (Core b n χ)), AlphaEq n (Coreχ b n χ)) => AlphaEq n (Core b n χ) where
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
    (Eqlχ _ tel ty v1 v2, Eqlχ _ tel' ty' v1' v2') ->
      let (tel_eq, rename') = αequal_tel rename tel tel'
      in tel_eq && αequal rename' ty ty' && αequal rename' v1 v1' && αequal rename' v2 v2'
    (Dapχ _ tel val, Dapχ _ tel' val') ->
      let (tel_eq, rename') = αequal_tel rename tel tel'
      in tel_eq && αequal rename' val val'
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

instance (Ord n, Binding b, AlphaEq n (b n (Core b n χ)), AlphaEq n (Coreχ b n χ)) => AlphaEq n (Module b n χ) where
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
