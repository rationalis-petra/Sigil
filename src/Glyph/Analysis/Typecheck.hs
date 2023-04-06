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

import Prettyprinter
import Prettyprinter.Render.Glyph

import Glyph.Abstract.Environment  
import Glyph.Abstract.Syntax  
import Glyph.Interpret.Substitution  
import Glyph.Concrete.Typed  

  
class Checkable n a | a -> n where 
  infer :: (Environment n e, MonadError GlyphDoc m) => e a -> a -> m a

  check :: (Environment n e, MonadError GlyphDoc m) => e a -> a -> a -> m ()

instance Checkable Name TypedCore where 
  infer env term = case term of
    Var _ n -> lookup_err n env
    Uni χ j -> pure $ Uni χ (j + 1)
    App _ l r -> do
      (AnnBind (n, arg_ty), ret_ty) <- infer env l >>= check_prod 
      check env r arg_ty
      pure $ subst (n ↦ r) ret_ty
  
    Abs _ (AnnBind (n, a)) body -> do
      ret_ty <- infer (insert n a env) body
      pure $ Prd () (AnnBind (n, a)) ret_ty
    _ -> throwError $ "infer not implemented for term:" <+> pretty term
      
  
    where 
      check_prod (Prd _ b ty) = pure (b, ty)
      check_prod term = throwError $ "expected prod, got:" <+> pretty term
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check env term ty = case (term, ty) of
    (Uni _ j, Uni _ k) 
      | j < k -> pure ()
      | otherwise -> throwError "universe-level check failed"
  
    -- TODO: generalize to more bindings; notably untyped bindings!!
    (Abs _ (AnnBind (n, a)) body, Prd _ (AnnBind (_,a')) ret_ty) -> do
      check_eq a a'
      check (insert n a env) body ret_ty
    (Abs _ _ _, _) -> throwError $ "expected λ-term to have Π-type, got" <+> pretty ty
  
    (Prd _ (AnnBind (n, a)) b, _) -> do
      check env a ty
      check (insert n a env) b ty
  
    _ -> do
      ty' <- infer env term
      check_eq ty ty'


-- TODO: replace with check_sub!!
check_eq :: (MonadError GlyphDoc m) => TypedCore -> TypedCore -> m ()
check_eq ty ty'
  -- TODO: replace with αβη-equality
  | ty == ty' = pure ()
  | otherwise = throwError $ "not-equal:" <+> pretty ty <+> "and" <+> pretty ty'
