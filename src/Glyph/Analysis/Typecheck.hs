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
import Glyph.Abstract.Substitution
import Glyph.Interpret.Term
import Glyph.Concrete.Resolved
import Glyph.Concrete.Internal

  
class Checkable n a t | a -> n t where 
  infer :: (Environment n e, MonadError GlyphDoc m, MonadGen m) => e (Maybe t,t) -> a -> m (t, t)
  check :: (Environment n e, MonadError GlyphDoc m, MonadGen m) => e (Maybe t,t) -> a -> t -> m t

instance Checkable Name InternalCore InternalCore where 
  infer env term = case term of
    Var n -> (\(_, ty) -> (term, ty)) <$> lookup_err n env
    Uni j -> pure (term, Uni (j + 1))
    App l r -> do
      (l', lty) <- infer env l
      (AnnBind (n, arg_ty), ret_ty) <- check_prod lty
      r' <- check env r arg_ty
      pure (App l' r', subst (n ↦ r) ret_ty)
  
    Abs (AnnBind (n, a)) body -> do
      (a', aty) <- infer env a
      a_norm <- normalize env aty a'

      let env' = insert n (Nothing, a_norm) env
      (body', ret_ty) <- infer env' body

      pure (Abs (AnnBind (n, a')) body', Prd (AnnBind (n, a')) ret_ty)

    Prd (AnnBind (n, a)) b -> do
      (a', aty) <- infer env a
      a_norm <- normalize env aty a'

      let env' = insert n (Nothing, a_norm) env
      (b', bty) <- infer env' b

      i <- check_lvl aty
      j <- check_lvl bty
      pure $ (Prd (AnnBind (n, a')) b', Uni (max i j))
  
    _ -> throwError $ "infer not implemented for term:" <+> pretty term
  
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check env term ty = case (term, ty) of
    (Uni j, Uni k)
      | j < k -> pure term
      | otherwise -> throwError "universe-level check failed"
  
    -- TODO: generalize to more bindings; notably untyped bindings!!
    (Abs (AnnBind (n, a)) body, Prd (AnnBind (_,a')) ret_ty) -> do
      check_eq a a'
      body' <- check (insert n (Nothing, a) env) body ret_ty
      pure $ Abs (AnnBind (n, a')) body'
    (Abs _ _, _) -> throwError $ "expected λ-term to have Π-type, got" <+> pretty ty
  
    (Prd (AnnBind (n, a)) b, _) -> do
      a' <- check env a ty
      b' <- check (insert n (Nothing, a) env) b ty
      pure $ Prd (AnnBind (n, a')) b'
  
    _ -> do
      (term', ty') <- infer env term
      check_eq ty ty'
      pure term'


instance Checkable Name ResolvedCore InternalCore where 
  infer env term = case term of
    Varχ _ n -> do
      ty <- snd <$> lookup_err n env
      pure $ (Var n, ty)
    Uniχ _ j -> pure $ (Uni j, Uni (j + 1))
    Appχ _ l r -> do
      (l', lty) <- infer env l
      (AnnBind (n, arg_ty), ret_ty) <- check_prod lty
      r' <- check env r arg_ty
      rnorm <- normalize env arg_ty r'
      pure $ (App l' r', subst (n ↦ rnorm) ret_ty)
  
    Absχ _ (OptBind (Just n, Just a)) body -> do
      (a', aty) <- infer env a
      a_norm <- normalize env aty a'

      let env' = insert n (Nothing, a_norm) env
      (body', ret_ty) <- infer env' body

      pure (Abs (AnnBind (n, a')) body', Prd (AnnBind (n, a')) ret_ty)

    Prdχ _ (OptBind (Just n, Just a)) b -> do
      (a', aty) <- infer env a
      a_norm <- normalize env aty a'

      let env' = insert n (Nothing, a_norm) env
      (b', bty) <- infer env' b

      i <- check_lvl aty
      j <- check_lvl bty
      pure $ (Prd (AnnBind (n, a')) b', Uni (max i j))
    _ -> throwError $ "infer not implemented for term:" <+> pretty term
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check env term ty = case (term, ty) of
    (Uniχ _ j, Uni k) 
      | j < k -> pure (Uni j)
      | otherwise -> throwError "universe-level check failed"
  
    -- TODO: generalize to more bindings; notably untyped bindings!!
    (Absχ _ (OptBind (Just n, Just a)) body, Prd (AnnBind (_,a')) ret_ty) -> do
      (a_typd, a_ty) <- infer env a
      a_normal <- normalize env a_ty a_typd
      check_eq a_normal a'
      body' <- check (insert n (Nothing, a_normal) env) body ret_ty
      pure $ Abs (AnnBind (n, a_normal)) body'
    (Absχ _ (OptBind (Just n, Nothing)) body, Prd (AnnBind (_,a')) ret_ty) -> do
      body' <- check (insert n (Nothing, a') env) body ret_ty
      pure $ Abs (AnnBind (n, a')) body'
    (Absχ _ _ _, _) -> throwError $ "expected λ-term to have Π-type, got" <+> pretty ty
  
    (Prdχ _ (OptBind (Just n, Just a)) b, _) -> do
      -- TODO: normalization??
      a' <- check env a ty
      b' <- check (insert n (Nothing, a') env) b ty
      pure $ Prd (AnnBind (n, a')) b'
                            
    (Prdχ _ _ _, _) -> throwError $ "expected Π-term to have a named binding, did not!" <+> pretty term
  
    _ -> do
      (term', ty') <- infer env term
      check_eq ty ty'
      pure term'


-- infer :: (Environment n e, MonadError GlyphDoc m, MonadGen m) =>
--          e (Maybe Core Name b χ', Core Name b χ') -> Transformer χ χ' -> Core Name b χ -> m (Core Name b χ', Core Name b χ')
-- infer (Transformerχ {..}) env term = case term of
--   Var _ n -> (\(_, ty) -> (term, ty)) <$> lookup_err n env
--   Uni χ j -> pure (Uni (tuni χ) j, Uni (tuni χ) (j + 1))
--   App χ l r -> do
--     (l', lty) <- infer env l
--     (AnnBind (n, arg_ty), ret_ty) <- check_prod lty
--     r' <- check env r arg_ty
--     pure (App (tapp χ) l' r', subst (n ↦ r) ret_ty)

--   Abs χ (AnnBind (n, a)) body -> do
--     (a', aty) <- infer env a
--     a_norm <- normalize env aty a'

--     let env' = insert n (Nothing, a_norm) env
--     (body', ret_ty) <- infer env' body

--     pure (Abs (tabs χ) (AnnBind (n, a')) body', Prd () (AnnBind (n, a')) ret_ty)

--   Prd χ (AnnBind (n, a)) b -> do
--     (a', aty) <- infer env a
--     a_norm <- normalize env aty a'

--     let env' = insert n (Nothing, a_norm) env
--     (b', bty) <- infer env' b

--     i <- check_lvl aty
--     j <- check_lvl bty
--     pure $ (Prd χ (AnnBind (n, a')) b', Uni () (max i j))

--   _ -> throwError $ "infer not implemented for term:" <+> pretty term
    

--   where 
--     check_prod (Prd _ b ty) = pure (b, ty)
--     check_prod term = throwError $ "expected prod, got:" <+> pretty term

--     check_lvl (Uni _ i) = pure i
--     check_lvl (Prd _ (AnnBind (_, a)) b) = max <$> check_lvl a <*> check_lvl b
--     check_lvl term = throwError $ "expected 𝒰ᵢ, got:" <+> pretty term
  
-- check :: (Environment n e, MonadError GlyphDoc m, MonadGen m) => e (Maybe t,t) -> a -> t -> m t
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



-- TODO: bad for internal core?
check_prod :: (MonadError (Doc ann) m, Pretty (Core b n χ)) => Core b n χ -> m (b n (Core b n χ), Core b n χ)
check_prod (Prdχ _ b ty) = pure (b, ty)
check_prod term = throwError $ "expected prod, got:" <+> pretty term

check_lvl :: (MonadError (Doc ann) m, Binding b, Pretty (Core b n χ)) => Core b n χ -> m Int
check_lvl (Uniχ _ i) = pure i
check_lvl term@(Prdχ _ bn b) = case tipe bn of
  Just a -> max <$> check_lvl a <*> check_lvl b
  Nothing -> throwError $ "expected 𝒰ᵢ, got:" <+> pretty term
check_lvl term = throwError $ "expected 𝒰ᵢ, got:" <+> pretty term
