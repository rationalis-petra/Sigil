module Glyph.Abstract.Substitution (
  Substitution,
  Subst(..),
  Regen(..)) where


{-------------------------------- SUBSTITUTION ---------------------------------}
{- This module contains the Subst typeclass, which supports two kinds of       -}
{- substitution:                                                               -}
{- 1. Regular, unnormalizing substitution.                                     -}
{- 2. Typed, hereditary substitution.                                          -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (lookup)
import Data.Maybe (fromMaybe)
import Data.Map (Map, empty)

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment


newtype Substitution a = Substitution (Map Integer a)
  deriving (Functor, Foldable)


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


class Subst n s a | a -> s n where
  subst :: Environment n e => e s -> a -> a
  
class Regen a where  
  regen :: MonadGen m => a -> m a
  

{--------------------------- SUBSTITUTION INSTANCES ----------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


instance Subst n s a => Subst n s (OptBind n a) where
  subst sub bind = case bind of
    OptBind (Left n) -> OptBind $ Left n
    OptBind (Right (n, a)) -> OptBind $ Right (n, (subst sub a))
  
instance Subst n s a => Subst n s (AnnBind n a) where
  subst sub (AnnBind (n, a)) = AnnBind (n, subst sub a)

instance Subst n (Core b n χ) (b n (Core b n χ))=> Subst n (Core b n χ) (Core b n χ) where 
  subst sub term = case term of
    Coreχ χ -> Coreχ χ 
    Uni χ n -> Uni χ n
    Var _ var -> fromMaybe term (lookup var sub)
    Prd χ bind ty ->
      Prd χ (subst sub bind) (subst sub ty)
    Abs χ bind body ->
      Abs χ (subst sub bind) (subst sub body)
    App χ l r -> App χ (subst sub l) (subst sub r)


instance Regen (Core OptBind Name χ) where 
  regen = go (Substitution empty) where
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
  regen = go (Substitution empty) where
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
