module Glyph.Abstract.Substitution (
  Substitution,
  Subst(..),
  subst,
  (↦),
  Regen(..)) where


{-------------------------------- SUBSTITUTION ---------------------------------}
{- This module contains the Subst typeclass, which supports two kinds of       -}
{- substitution:                                                               -}
{- 1. Regular, unnormalizing substitution.                                     -}
{- 2. Typed, hereditary substitution.                                          -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (lookup)
import Data.Foldable 
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment


newtype Substitution a = Substitution (Map Integer a)
  deriving (Functor, Foldable)

class Subst n s a | a -> s n where
  substitute :: Environment n e => Set n -> e s -> a -> a
  free_vars :: a -> Set n
  
class Regen a where  
  regen :: MonadGen m => a -> m a
  
subst :: (Subst n s a, Environment n e) => e s -> a -> a
subst = substitute Set.empty

(↦) :: Name -> a -> Substitution a
n ↦ v = insert n v env_empty

instance Subst Name a a => Semigroup (Substitution a) where
  (Substitution m1) <> (Substitution m2) =
    Substitution $ Map.union m2 $ fmap (subst m2) m1

instance Subst Name a a => Monoid (Substitution a) where
  mempty = Substitution Map.empty

instance Environment Name Substitution where
  lookup_err var (Substitution env) =
    lookup_err var env

  lookup var (Substitution env) =
    lookup var env

  insert n val (Substitution env) =
    Substitution $ insert n val env

  env_empty =
    Substitution env_empty

  eval_helper eval (Substitution s) =
    let eval' v env = eval v (Substitution env)
    in Substitution <$> eval_helper eval' s

{--------------------------- SUBSTITUTION INSTANCES ----------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


instance (Ord n, Subst n s a) => Subst n s [a] where 
  substitute shadow sub = fmap (substitute shadow sub)

  free_vars = foldl' Set.union Set.empty . fmap free_vars  

instance (Ord n, Subst n s a) => Subst n s (OptBind n a) where
  substitute shadow sub bind = case bind of
    OptBind (Left _) -> bind
    OptBind (Right (n, a)) ->
      OptBind $ Right (n, (substitute (Set.insert n shadow) sub a))

  free_vars bind = case bind of 
    OptBind (Left _) -> Set.empty
    OptBind (Right (n, a)) -> Set.delete n $ free_vars a
  
instance (Ord n, Subst n s a) => Subst n s (AnnBind n a) where
  substitute shadow sub (AnnBind (n, a)) =
    AnnBind (n, substitute (Set.insert n shadow) sub a)

  free_vars (AnnBind (n, a)) =
    Set.delete n $ free_vars a

instance (Ord n, Binding b,
          Subst n (Core b n χ) (b n (Core b n χ)))
          => Subst n (Core b n χ) (Core b n χ) where 
  substitute shadow sub term = case term of
    Coreχ χ -> Coreχ χ 
    Uni χ n -> Uni χ n
    Var _ var ->
      if Set.member var shadow then
        term
      else
        fromMaybe term (lookup var sub)
    Prd χ bind ty ->
      Prd χ (substitute shadow sub bind) (substitute shadow' sub ty)
      where
        shadow' = Set.insert (name bind) shadow
    Abs χ bind body ->
      Abs χ (substitute shadow sub bind) (substitute shadow' sub body)
      where
        shadow' = Set.insert (name bind) shadow
    App χ l r -> App χ (substitute shadow sub l) (substitute shadow sub r)

  free_vars term = case term of 
    Coreχ _ -> Set.empty
    Uni _ _ -> Set.empty
    Var _ var -> Set.singleton var
    Prd _ bind ty -> 
      Set.union (free_vars bind) (Set.delete (name bind) (free_vars ty))
    Abs _ bind body ->
      Set.union (free_vars bind) (Set.delete (name bind) (free_vars body))
    App _ l r -> Set.union (free_vars l) (free_vars r)


instance Regen (Core OptBind Name χ) where 
  regen = go (Substitution Map.empty) where
    freshen_bind (OptBind (Left n)) sub = do
      n' <- freshen n
      pure (insert n n' sub, OptBind $ Left n')
    freshen_bind (OptBind (Right (n, ty))) sub = do
      n' <- freshen n
      let sub' = insert n n' sub
      ty' <- go sub ty
      pure (sub', OptBind $ Right (n', ty'))

    go sub term = case term of 
      Coreχ χ -> pure $ Coreχ χ 
      Uni χ n -> pure $ Uni χ n
      Var χ var -> case lookup var sub of 
        Just n' -> pure $ Var χ n'
        Nothing -> pure term
      Prd χ bind ty -> do
        (sub', bind') <- freshen_bind bind sub
        Prd χ bind' <$> (go sub' ty)
      Abs χ bind body -> do
        (sub', bind') <- freshen_bind bind sub
        Abs χ bind' <$> (go sub' body)
      App χ l r -> App χ <$> (go sub l) <*> (go sub r)

instance Regen (Core AnnBind Name χ) where 
  regen = go (Substitution Map.empty) where
    freshen_bind (AnnBind (n, ty)) sub = do
      n' <- freshen n
      let sub' = insert n n' sub
      ty' <- go sub' ty
      pure (sub', AnnBind (n', ty'))

    go sub term = case term of 
      Coreχ χ -> pure $ Coreχ χ 
      Uni χ n -> pure $ Uni χ n
      Var χ var -> case lookup var sub of 
        Just n' -> pure $ Var χ n'
        Nothing -> pure term
      Prd χ bind ty -> do
        (sub', bind') <- freshen_bind bind sub
        Prd χ bind' <$> (go sub' ty)
      Abs χ bind body -> do
        (sub', bind') <- freshen_bind bind sub
        Abs χ bind' <$> (go sub' body)
      App χ l r -> App χ <$> (go sub l) <*> (go sub r)
