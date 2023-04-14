module Glyph.Analysis.Typecheck
  ( Checkable(..) ) where


{-------------------------------- TYPECHECKING ---------------------------------}
{- The typechecker implemented here is a bidirectional type-checker.           -}
{- see:                                                                        -}
{-https://boxbase.org/entries/2019/jul/29/bidirectional-typechecking-dependent/-}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Control.Monad.Except (MonadError, throwError)
-- import qualified Data.Map as Map
-- import Data.Map (Map)  
-- import qualified Data.Text as Text

import Prettyprinter
import Prettyprinter.Render.Glyph

import Glyph.Abstract.Environment
import Glyph.Abstract.Syntax
import Glyph.Abstract.AlphaEq  
import Glyph.Interpret.Substitution
import Glyph.Interpret.Term
import Glyph.Concrete.Resolved
import Glyph.Concrete.Typed

  
class Checkable n a t | a -> n t where 
  infer :: (Environment n e, MonadError GlyphDoc m, MonadGen m) => e (t,t) -> a -> m (t, t)
  check :: (Environment n e, MonadError GlyphDoc m, MonadGen m) => e (t,t) -> a -> t -> m t

instance Checkable Name TypedCore TypedCore where 
  infer env term = case term of
    Var _ n -> (\(_, ty) -> (term, ty)) <$> lookup_err n env
    Uni χ j -> pure (term, Uni χ (j + 1))
    App χ l r -> do
      (l', lty) <- infer env l
      (AnnBind (n, arg_ty), ret_ty) <- check_prod lty
      r' <- check env r arg_ty
      pure (App χ l' r', subst (n ↦ r) ret_ty)
  
    Abs χ (AnnBind (n, a)) body -> do
      (body', ret_ty) <- infer (insert n (Var () n, a) env) body
      pure (Abs χ (AnnBind (n, a)) body', Prd () (AnnBind (n, a)) ret_ty)
    _ -> throwError $ "infer not implemented for term:" <+> pretty term
      
  
    where 
      check_prod (Prd _ b ty) = pure (b, ty)
      check_prod term = throwError $ "expected prod, got:" <+> pretty term
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check env term ty = case (term, ty) of
    (Uni _ j, Uni _ k)
      | j < k -> pure term
      | otherwise -> throwError "universe-level check failed"
  
    -- TODO: generalize to more bindings; notably untyped bindings!!
    (Abs χ (AnnBind (n, a)) body, Prd _ (AnnBind (_,a')) ret_ty) -> do
      check_eq a a'
      body' <- check (insert n (Var () n, a) env) body ret_ty
      pure $ Abs χ (AnnBind (n, a')) body'
    (Abs _ _ _, _) -> throwError $ "expected λ-term to have Π-type, got" <+> pretty ty
  
    (Prd χ (AnnBind (n, a)) b, _) -> do
      a' <- check env a ty
      b' <- check (insert n (Var () n, a) env) b ty
      pure $ Prd χ (AnnBind (n, a')) b'
  
    _ -> do
      (term', ty') <- infer env term
      check_eq ty ty'
      pure term'


instance Checkable Name ResolvedCore TypedCore where 
  infer env term = case term of
    Var _ n -> do
      ty <- snd <$> lookup_err n env
      pure $ (Var () n, ty)
    Uni _ j -> pure $ (Uni () j, Uni () (j + 1))
    App _ l r -> do
      (l', lty) <- infer env l
      (AnnBind (n, arg_ty), ret_ty) <- check_prod lty
      r' <- check env r arg_ty
      rnorm <- norm env arg_ty r'
      pure $ (App () l' r', subst (n ↦ rnorm) ret_ty)
  
    Abs _ (OptBind (Just n, Just a)) body -> do
      (a', aty) <- infer env a
      a_norm <- norm env aty a'
      (body', ret_ty) <- infer (insert n (Var mempty n, a_norm) env) body
      pure (Abs () (AnnBind (n, a_norm)) body', Prd () (AnnBind (n, a_norm)) ret_ty)
    _ -> throwError $ "infer not implemented for term:" <+> pretty term
      
  
    where 
      check_prod (Prd _ b ty) = pure (b, ty)
      check_prod term = throwError $ "expected prod, got:" <+> pretty term
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check env term ty = case (term, ty) of
    (Uni _ j, Uni _ k) 
      | j < k -> pure (Uni () j)
      | otherwise -> throwError "universe-level check failed"
  
    -- TODO: generalize to more bindings; notably untyped bindings!!
    (Abs _ (OptBind (Just n, Just a)) body, Prd _ (AnnBind (_,a')) ret_ty) -> do
      (a_typd, a_ty) <- infer env a
      a_normal <- norm env a_ty a_typd
      check_eq a_normal a'
      body' <- check (insert n (Var mempty n, a_normal) env) body ret_ty
      pure $ Abs () (AnnBind (n, a_normal)) body'
    (Abs _ (OptBind (Just n, Nothing)) body, Prd _ (AnnBind (_,a')) ret_ty) -> do
      body' <- check (insert n (Var mempty n, a') env) body ret_ty
      pure $ Abs () (AnnBind (n, a')) body'
    (Abs _ _ _, _) -> throwError $ "expected λ-term to have Π-type, got" <+> pretty ty
  
    (Prd _ (OptBind (Just n, Just a)) b, _) -> do
      -- TODO: normalization??
      a' <- check env a ty
      b' <- check (insert n (Var mempty n, a') env) b ty
      pure $ Prd () (AnnBind (n, a')) b'
                            
    (Prd _ _ _, _) -> throwError $ "expected Π-term to have a named binding, did not!" <+> pretty term
  
    _ -> do
      (term', ty') <- infer env term
      check_eq ty ty'
      pure term'

norm :: (MonadError (Doc ann) m, Environment Name e) =>
              e (TypedCore, TypedCore) -> TypedCore -> TypedCore -> m TypedCore
norm = normalize . fmap fst

-- fresh_name :: MonadGen m => m Name
-- fresh_name = fresh_id >>= \id -> pure $ Name $ Right (id, "*" <> Text.pack (show id))

-- freshen :: MonadGen m => Maybe Name -> m Name
-- freshen = maybe fresh_name pure

-- TODO: replace with check_sub!!
check_eq :: (MonadError GlyphDoc m, AlphaEq n a, Pretty a) => a -> a -> m ()
check_eq ty ty'
  -- TODO: replace with αβη-equality
  | αeq ty ty' = pure ()
  | otherwise = throwError $ "not-equal:" <+> pretty ty <+> "and" <+> pretty ty'

