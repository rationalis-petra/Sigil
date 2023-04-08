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

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment


class AlphaEq n a | a -> n where
  αequal :: (Map n n, Map n n) -> a -> a -> Bool

αeq :: AlphaEq n a => a -> a -> Bool
αeq = αequal (Map.empty, Map.empty)

-- (Ord n, AlphaEq n (b n (Core b n χ)))
instance (Ord n, Binding b, AlphaEq n (Core b n χ), AlphaEq n (b n (Core b n χ))) => AlphaEq n (Definition b n χ) where
  αequal rename v1 v2 = case (v1, v2) of 
    (Mutual defs, Mutual defs') -> is_eq . gather_rename rename $ (zip defs defs')
      where 
        is_eq (rename, defs) = foldl' (&&) True $ map (uncurry $ αequal rename) defs

        gather_rename rename [] = (rename, [])
        gather_rename rename (((b, v), (b', v')) : xs) = 
          (_2 %~ (:) (v, v')) $ gather_rename rename' xs
          where rename' =
                  ( Map.insert (name b) (name b') (fst rename)
                  , Map.insert (name b') (name b) (snd rename) )
          
      --foldl' (\ren ((b1,v1), (b2, v2)) -> case  ) rename (zip defs defs')
    -- (SigDef itype bind fields, SigDef itype' bind' fields') ->
    --   itype == itype' && bind == bind' && fields == fields'
    -- (IndDef itype bind terms, IndDef itype' bind' terms') ->
    --   itype == itype' && bind == bind' && terms == terms'
    (_, _) -> False

instance (Ord n, Binding b, AlphaEq n (b n (Core b n χ)), AlphaEq n (Coreχ b n χ)) => AlphaEq n (Core b n χ) where
  αequal rename v v' = case (v, v') of 
    (Coreχ r, Coreχ r') ->
      αequal rename r r'
    (Uni _ n, Uni _ n') -> n == n'
    (Var _ n, Var _ n') ->
      case (Map.lookup n (fst rename), Map.lookup n' (snd rename)) of
        (Just r, Just r') -> r == n' && r' == n
        (Nothing, Nothing) -> n == n'
        _ -> False
    (Prd _ b t, Prd _ b' t') ->
           αequal rename b b'
        && αequal rename' t t'
      where
        rename' = ( Map.insert (name b) (name b') (fst rename)
                  , Map.insert (name b') (name b) (snd rename) )
    (Abs _ b e, Abs _ b' e') ->
           αequal rename b b'
        && αequal rename' e e'
      where
        rename' = ( Map.insert (name b) (name b') (fst rename)
                  , Map.insert (name b') (name b) (snd rename) )
    (App _ l r, App _ l' r') ->
         αequal rename l l'
      && αequal rename r r'
    (_, _) -> False


instance (Ord n, AlphaEq n (Core OptBind n χ)) => AlphaEq n (OptBind n (Core OptBind n χ)) where
  αequal rename (OptBind b1) (OptBind b2) = case (b1, b2) of 
    (Right (n, ty), Right (n', ty')) -> αequal rename' ty ty'
      where
        rename' = (Map.insert n n' (fst rename), Map.insert n' n (snd rename))
    (Left _, Left _) -> True
    _ -> False

instance (Ord n, AlphaEq n (Core AnnBind n χ)) => AlphaEq n (AnnBind n (Core AnnBind n χ)) where
  αequal rename (AnnBind (n, ty)) (AnnBind (n', ty')) = αequal rename' ty ty' 
    where 
      rename' = (Map.insert n n' (fst rename), Map.insert n' n (snd rename))
    
