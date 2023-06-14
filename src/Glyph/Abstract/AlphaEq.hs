module Glyph.Abstract.AlphaEq
  ( AlphaEq(..)
  , αeq ) where

{-------------------------------- αEQ INSTANCE ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Control.Lens
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (foldl')


{------------------------------- Alpha Equality --------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}
  

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment


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

instance (Ord n, Binding b, AlphaEq n (Core b n χ), AlphaEq n (b n (Core b n χ))) => AlphaEq n (Definition b n χ) where
  αequal rename v1 v2 = case (v1, v2) of 
    (Mutualχ _ defs, Mutualχ _ defs') -> is_eq . gather_rename rename $ (zip defs defs')
      where 
        is_eq (rename, defs) = foldl' (&&) True $ map (uncurry $ αequal rename) defs

        gather_rename rename [] = (rename, [])
        gather_rename rename (((b, v), (b', v')) : xs) = 
          (_2 %~ (:) (v, v')) $ gather_rename rename' xs
          where rename' =
                  ( maybe (fst rename) (\n -> Map.insert n (name b') (fst rename)) (name b)
                  , maybe (snd rename) (\n -> Map.insert n (name b) (snd rename)) (name b'))
          
    -- TODO: other definition types!
    -- (SigDef itype bind fields, SigDef itype' bind' fields') ->
    --   itype == itype' && bind == bind' && fields == fields'
    -- (IndDef itype bind terms, IndDef itype' bind' terms') ->
    --   itype == itype' && bind == bind' && terms == terms'
    (_, _) -> False

instance (Ord n, Binding b, AlphaEq n (b n (Core b n χ)), AlphaEq n (Coreχ b n χ)) => AlphaEq n (Core b n χ) where
  αequal rename v v' = case (v, v') of 
    (Coreχ r, Coreχ r') ->
      αequal rename r r'
    (Uniχ _ n, Uniχ _ n') -> n == n'
    (Varχ _ n, Varχ _ n') ->
      case (Map.lookup n (fst rename), Map.lookup n' (snd rename)) of
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
    (_, _) -> False

instance (Ord n, Binding b, AlphaEq n (Core b n χ)) => AlphaEq n (b n (Core b n χ)) where
  αequal rename b b' = case (tipe b, tipe b') of 
    (Just ty, Just ty') -> αequal rename' ty ty'
      where
        rename' = ( maybe (fst rename) (\n -> Map.insert n (name b') (fst rename)) (name b)
                  , maybe (snd rename) (\n -> Map.insert n (name b) (snd rename)) (name b'))
    (Nothing, Nothing) -> True
    _ -> False

instance AlphaEq Name () where
  αequal _ _ _ = True
