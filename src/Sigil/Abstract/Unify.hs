 module Sigil.Abstract.Unify
   ( SingleConstraint(..)
   , Quant(..)
   , Formula(..) ) where

import qualified Data.Set as Set
import qualified Data.List as List

import Prettyprinter

import Sigil.Abstract.Names
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


-- class Unifiable m a | a -> m where
--   solve :: Formula a -> m (Substitution a)
  -- solve_isolated :: Env a -> Formula a -> Either (Doc ann) (Substitution a)

data SingleConstraint a
  = a :≗: a -- Claim of Unifiability of two terms
  | a :∈: a -- Claim of type occupation 

data Quant = Exists | Forall
  deriving (Eq, Ord)

data Formula a
  = Conj [SingleConstraint a]     -- Conjuntion of n single constraints ([] = ⊤)
  | And (Formula a) (Formula a)   -- Conjunction of two formulas
  | Bind Quant Name a (Formula a) -- Quantified (∀/∃) formulas


instance Functor SingleConstraint where  
  fmap f con = case con of 
    a :≗: b -> f a :≗: f b
    a :∈: b -> f a :∈: f b

instance Subst Name s a => Subst Name s (SingleConstraint a) where  
  substitute shadow sub con = fmap (substitute shadow sub) con

  free_vars con = case con of
    a :≗: b -> Set.union (free_vars a) (free_vars b)
    a :∈: b -> Set.union (free_vars a) (free_vars b)

instance (Subst Name s a) => Subst Name s (Formula a) where
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
    a :≗: b -> "(" <> pretty a <+> "≗" <+> pretty b <> ")"
    a :∈: ty -> "(" <> pretty a <+> "∈" <+> pretty ty <> ")"

instance Pretty a => Pretty (Formula a) where
  pretty f = case f of 
    Conj fs -> case fs of 
      [] -> "⊤"
      _ -> (foldl (<+>) "" . List.intersperse "∧" . map pretty) fs
    And l r ->
      "(" <> pretty l <+> "∧" <+> pretty r <> ")"
    Bind quant nm ty f' ->
      pretty quant <> pretty nm <> ":" <+> pretty ty <> "." <+> pretty f'
