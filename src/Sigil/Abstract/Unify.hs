{-# OPTIONS_GHC -XDeriveAnyClass #-}
 module Sigil.Abstract.Unify
   ( SingleConstraint(..)
   , Quant(..)
   , Formula(..) ) where

import Data.Functor.Classes 
import qualified Data.Set as Set
import qualified Data.List as List

import Prettyprinter

import Sigil.Abstract.Substitution


{------------------------------ TYPE DEFINITIONS -------------------------------}
{- The types here are for the most part direct translations of types mentioned -}
{- above, and form the public interface to this module.                        -}
{-                                                                             -}
{- Note the slight modification to the Formula Type - it is now split in two:  -}
{- SingleConstraint, and Formula. This is because many helper functions.       -}
{- Focus on solving one (or more) single constraints, and so having a separate -}
{- type for them makes giving types to these functions easier.                 -}
{-                                                                             -}
{- The Unifiable typeclass represents terms which can be unified when placed   -}
{- in a formula, and is based on the solve. Method.                            -}
{-------------------------------------------------------------------------------}


data SingleConstraint a
  = a :≗: a -- Claim of Unifiability of two terms
  | a :∈: a -- Claim of type occupation 
  deriving (Eq)

data Quant = Exists | Forall
  deriving (Eq, Ord)

data Formula n a
  = Conj [SingleConstraint a]     -- Conjuntion of n single constraints ([] = ⊤)
  | And (Formula n a) (Formula n a)   -- Conjunction of two formulas
  | Bind Quant n a (Formula n a) -- Quantified (∀/∃) formulas
  deriving (Eq)


instance Functor SingleConstraint where  
  fmap f con = case con of 
    a :≗: b -> f a :≗: f b
    a :∈: b -> f a :∈: f b

instance (Subst n s a, Ord n) => Subst n s (SingleConstraint a) where  
  substitute shadow sub con = fmap (substitute shadow sub) con

  free_vars con = case con of
    a :≗: b -> Set.union (free_vars a) (free_vars b)
    a :∈: b -> Set.union (free_vars a) (free_vars b)

instance Eq1 SingleConstraint where
  liftEq eq l r = case (l,r) of 
    (l :≗: l', r :≗: r') -> eq l r && eq l' r' 
    (l :∈: l', r :∈: r') -> eq l r && eq l' r' 
    _ -> False

instance Eq n => Eq1 (Formula n) where
  liftEq eq l r = case (l,r) of 
    (Conj l1, Conj l2) -> liftEq (liftEq eq) l1 l2
    (And l r, And l' r') -> liftEq eq l l' && liftEq eq r r'
    (Bind q n ty f, Bind q' n' ty' f') ->
      q == q' && n == n' && eq ty ty' && liftEq eq f f' 
    _ -> False

instance Eq2 Formula where
  liftEq2 eq eq' l r = case (l,r) of 
    (Conj l1, Conj l2) -> liftEq (liftEq eq') l1 l2
    (And l r, And l' r') -> liftEq2 eq eq' l l' && liftEq2 eq eq' r r'
    (Bind q n ty f, Bind q' n' ty' f') ->
      q == q' && eq n n' && eq' ty ty' && liftEq2 eq eq' f f' 
    _ -> False

instance (Subst n s a, Ord n) => Subst n s (Formula n a) where
  substitute shadow sub term = case term of 
    Conj l ->
      Conj $ fmap (substitute shadow sub) l
    And l r ->
      And (substitute shadow sub l) (substitute shadow sub r)
    Bind quant var ty body ->
      Bind quant var (substitute shadow' sub ty) (substitute shadow' sub body)
      where shadow' = Set.insert var shadow

  free_vars form = case form of
    Conj l ->
      List.foldl' Set.union Set.empty $ fmap free_vars l
    And l r ->
      Set.union (free_vars l) (free_vars r)
    Bind _ var ty body ->
      Set.union (free_vars ty) $ Set.delete var (free_vars body)


{------------------------------ PRETTY INSTANCES -------------------------------}


instance Pretty Quant where 
  pretty Exists = "∃"
  pretty Forall = "∀"

instance Pretty a => Pretty (SingleConstraint a) where  
  pretty s = case s of 
    a :≗: b -> pretty a <+> "≅" <+> pretty b
    a :∈: ty -> pretty a <+> "∈" <+> pretty ty

instance (Pretty a, Pretty n) => Pretty (Formula n a) where
  pretty f = case f of 
    Conj fs -> case fs of 
      [] -> "⊤"
      _ -> (foldl (<+>) "" . List.intersperse "∧" . map pretty) fs
    And l r ->
      "(" <> pretty l <+> "∧" <+> pretty r <> ")"
    Bind quant nm ty f' ->
      pretty quant <> pretty nm <> "⮜" <+> pretty ty <> "." <+> pretty f'
