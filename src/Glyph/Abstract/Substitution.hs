module Glyph.Abstract.Substitution
  ( Substitution
  , Subst(..)
  , subst
  , (↦)
  , Regen(..) ) where


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
import qualified Data.Set as Set
import Data.Set (Set)

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment


newtype Substitution a = Substitution (Env a)
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
    Substitution $ union m2 $ fmap (subst m2) m1

instance Subst Name a a => Monoid (Substitution a) where
  mempty = Substitution env_empty

instance Environment Name Substitution where
  lookup_err var (Substitution env) =
    lookup_err var env

  lookup var (Substitution env) =
    lookup var env

  insert n val (Substitution env) =
    Substitution $ insert n val env

  union (Substitution l) (Substitution r) = 
    Substitution (union l r)

  env_empty =
    Substitution env_empty

  eval_helper eval (Substitution s) =
    let eval' n v env = eval n v (Substitution env)
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
  substitute shadow sub (OptBind (n, ty)) = substitute shadow' sub (OptBind (n, ty'))
    where
      shadow' = maybe shadow (flip Set.insert shadow) n
      ty' = fmap (substitute shadow' sub) ty 

  free_vars (OptBind (n, ty)) =
    maybe id Set.delete n $ fromMaybe Set.empty (free_vars <$> ty)
  
instance (Ord n, Subst n s a) => Subst n s (AnnBind n a) where
  substitute shadow sub (AnnBind (n, a)) = AnnBind (n, substitute shadow'  sub a)
    where
      -- shadow' = maybe shadow (flip Set.insert shadow) n
      shadow' = Set.insert n shadow

  free_vars (AnnBind (n, a)) = Set.delete n $ free_vars a
    --maybe id Set.delete n $ free_vars a

instance (Ord n, Binding b,
          Subst n (Core b n χ) (b n (Core b n χ)))
          => Subst n (Core b n χ) (Core b n χ) where 
  substitute shadow sub term = case term of
    Coreχ χ -> Coreχ χ 
    Uniχ χ n -> Uniχ χ n
    Varχ _ var ->
      if Set.member var shadow then
        term
      else
        fromMaybe term (lookup var sub)
    Prdχ χ bind ty ->
      Prdχ χ (substitute shadow sub bind) (substitute shadow' sub ty)
      where
        shadow' = maybe shadow (\n -> Set.insert n shadow) (name bind)
    Absχ χ bind body ->
      Absχ χ (substitute shadow sub bind) (substitute shadow' sub body)
      where
        shadow' = maybe shadow (\n -> Set.insert n shadow) (name bind)
    Appχ χ l r -> Appχ χ (substitute shadow sub l) (substitute shadow sub r)

  free_vars term = case term of 
    Coreχ _ -> Set.empty
    Uniχ _ _ -> Set.empty
    Varχ _ var -> Set.singleton var
    Prdχ _ bind ty -> let fvt = free_vars ty in
      Set.union (free_vars bind) (maybe fvt (\n -> Set.delete n fvt) (name bind))
    Absχ _ bind body -> let fvb = free_vars body in
      Set.union (free_vars bind) (maybe fvb (\n -> Set.delete n fvb) (name bind))
    Appχ _ l r -> Set.union (free_vars l) (free_vars r)


instance Regen (Core OptBind Name χ) where 
  regen = go (Substitution env_empty) where
    freshen_bind (OptBind (n, ty)) sub = do
      n' <- mapM freshen n
      let sub' = maybe sub (flip (uncurry insert) sub) ((,) <$> n <*> n')
      ty' <- mapM (go sub) ty
      pure (sub', OptBind (n', ty'))

    go sub term = case term of 
      Coreχ χ -> pure $ Coreχ χ 
      Uniχ χ n -> pure $ Uniχ χ n
      Varχ χ var -> case lookup var sub of 
        Just n' -> pure $ Varχ χ n'
        Nothing -> pure term
      Prdχ χ bind ty -> do
        (sub', bind') <- freshen_bind bind sub
        Prdχ χ bind' <$> (go sub' ty)
      Absχ χ bind body -> do
        (sub', bind') <- freshen_bind bind sub
        Absχ χ bind' <$> (go sub' body)
      Appχ χ l r -> Appχ χ <$> (go sub l) <*> (go sub r)

instance Regen (Core AnnBind Name χ) where 
  regen = go (Substitution env_empty) where
    freshen_bind (AnnBind (n, ty)) sub = do
      n' <- freshen n
      let sub' = insert n n' sub
      ty' <- go sub' ty
      pure (sub', AnnBind (n', ty'))
      -- n' <- mapM freshen n
      -- let sub' = maybe sub (flip (uncurry insert) sub) ((,) <$> n <*> n')
      -- ty' <- go sub' ty
      -- pure (sub', AnnBind (n', ty'))

    go sub term = case term of 
      Coreχ χ -> pure $ Coreχ χ 
      Uniχ χ n -> pure $ Uniχ χ n
      Varχ χ var -> case lookup var sub of 
        Just n' -> pure $ Varχ χ n'
        Nothing -> pure term
      Prdχ χ bind ty -> do
        (sub', bind') <- freshen_bind bind sub
        Prdχ χ bind' <$> (go sub' ty)
      Absχ χ bind body -> do
        (sub', bind') <- freshen_bind bind sub
        Absχ χ bind' <$> (go sub' body)
      Appχ χ l r -> Appχ χ <$> (go sub l) <*> (go sub r)
