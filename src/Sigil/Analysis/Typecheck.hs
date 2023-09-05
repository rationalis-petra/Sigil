module Sigil.Analysis.Typecheck
  ( Checkable(..)
  , check_entry
  , check_module
  ) where


{-------------------------------- TYPECHECKING ---------------------------------}
{- The typechecker implemented here is a bidirectional type-checker.           -}
{- see:                                                                        -}
{-https://boxbase.org/entries/2019/jul/29/bidirectional-typechecking-dependent/-}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Control.Monad.Except (MonadError, throwError)
import Control.Lens
import Data.Foldable
-- import qualified Data.Map as Map
-- import Data.Map (Map)  
-- import qualified Data.Text as Text

import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Environment
import Sigil.Abstract.Syntax
import Sigil.Abstract.AlphaEq  
import Sigil.Abstract.Substitution
import Sigil.Concrete.Resolved
import Sigil.Concrete.Internal


type Evaluator m e t = e (Maybe t,t) -> t -> t -> m t
  
class Checkable n a t | a -> n t where 
  infer :: (Environment n e, MonadError SigilDoc m, MonadGen m) => Evaluator m e t -> e (Maybe t,t) -> a -> m (t, t)
  check :: (Environment n e, MonadError SigilDoc m, MonadGen m) => Evaluator m e t -> e (Maybe t,t) -> a -> t -> m t

instance Checkable Name InternalCore InternalCore where 
  infer normalize env term = case term of
    Var n -> (\(_, ty) -> (term, ty)) <$> lookup_err n env
    Uni j -> pure (term, Uni (j + 1))
    App l r -> do
      (l', lty) <- infer normalize env l
      (AnnBind (n, arg_ty), ret_ty) <- check_prod lty
      r' <- check normalize env r arg_ty
      pure (App l' r', subst (n ↦ r) ret_ty)
  
    Abs (AnnBind (n, a)) body -> do
      (a', aty) <- infer normalize env a
      a_norm <- normalize env aty a'

      let env' = insert n (Nothing, a_norm) env
      (body', ret_ty) <- infer normalize env' body

      pure (Abs (AnnBind (n, a')) body', Prd (AnnBind (n, a')) ret_ty)

    Prd (AnnBind (n, a)) b -> do
      (a', aty) <- infer normalize env a
      a_norm <- normalize env aty a'

      let env' = insert n (Nothing, a_norm) env
      (b', bty) <- infer normalize env' b

      i <- check_lvl aty
      j <- check_lvl bty
      pure (Prd (AnnBind (n, a')) b', Uni (max i j))
  
    _ -> throwError $ "infer not implemented for term:" <+> pretty term
  
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check normalize env term ty = case (term, ty) of
    (Uni j, Uni k)
      | j < k -> pure term
      | otherwise -> throwError "universe-level check failed"
  
    -- TODO: generalize to more bindings; notably untyped bindings!!
    (Abs (AnnBind (n, a)) body, Prd (AnnBind (_,a')) ret_ty) -> do
      check_eq a a'
      body' <- check normalize (insert n (Nothing, a) env) body ret_ty
      pure $ Abs (AnnBind (n, a')) body'
    (Abs _ _, _) -> throwError $ "expected λ-term to have Π-type, got" <+> pretty ty
  
    (Prd (AnnBind (n, a)) b, _) -> do
      a' <- check normalize env a ty
      b' <- check normalize (insert n (Nothing, a) env) b ty
      pure $ Prd (AnnBind (n, a')) b'
  
    _ -> do
      (term', ty') <- infer normalize env term
      check_eq ty ty'
      pure term'


instance Checkable Name ResolvedCore InternalCore where 
  infer normalize env term = case term of
    Varχ _ n -> do
      ty <- snd <$> lookup_err n env
      pure (Var n, ty)
    Uniχ _ j -> pure (Uni j, Uni (j + 1))
    Appχ _ l r -> do
      (l', lty) <- infer normalize env l
      (AnnBind (n, arg_ty), ret_ty) <- check_prod lty
      r' <- check normalize env r arg_ty
      rnorm <- normalize env arg_ty r'
      pure (App l' r', subst (n ↦ rnorm) ret_ty)
  
    Absχ _ (OptBind (Just n, Just a)) body -> do
      (a', aty) <- infer normalize env a
      a_norm <- normalize env aty a'

      let env' = insert n (Nothing, a_norm) env
      (body', ret_ty) <- infer normalize env' body

      pure (Abs (AnnBind (n, a')) body', Prd (AnnBind (n, a')) ret_ty)

    Prdχ _ (OptBind (Just n, Just a)) b -> do
      (a', aty) <- infer normalize env a
      a_norm <- normalize env aty a'

      let env' = insert n (Nothing, a_norm) env
      (b', bty) <- infer normalize env' b

      i <- check_lvl aty
      j <- check_lvl bty
      pure (Prd (AnnBind (n, a')) b', Uni (max i j))
    _ -> throwError $ "infer not implemented for term:" <+> pretty term
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check normalize env term ty = case (term, ty) of
    (Uniχ _ j, Uni k) 
      | j < k -> pure (Uni j)
      | otherwise -> throwError "universe-level check failed"
  
    -- TODO: generalize to more bindings; notably untyped bindings!!
    (Absχ _ (OptBind (Just n, Just a)) body, Prd (AnnBind (_,a')) ret_ty) -> do
      (a_typd, a_ty) <- infer normalize env a
      a_normal <- normalize env a_ty a_typd
      check_eq a_normal a'
      body' <- check normalize (insert n (Nothing, a_normal) env) body ret_ty
      pure $ Abs (AnnBind (n, a_normal)) body'
    (Absχ _ (OptBind (Just n, Nothing)) body, Prd (AnnBind (_,a')) ret_ty) -> do
      body' <- check normalize (insert n (Nothing, a') env) body ret_ty
      pure $ Abs (AnnBind (n, a')) body'
    (Absχ {}, _) -> throwError $ "expected λ-term to have Π-type, got" <+> pretty ty
  
    (Prdχ _ (OptBind (Just n, Just a)) b, _) -> do
      -- TODO: normalization??
      a' <- check normalize env a ty
      b' <- check normalize (insert n (Nothing, a') env) b ty
      pure $ Prd (AnnBind (n, a')) b'
                            
    (Prdχ {}, _) -> throwError $ "expected Π-term to have a named binding, did not!" <+> pretty term
  
    _ -> do
      (term', ty') <- infer normalize env term
      check_eq ty ty'
      pure term'

check_entry :: (Environment Name e, MonadError SigilDoc m, MonadGen m) => Evaluator m e InternalCore -> e (Maybe InternalCore, InternalCore)
  -> ResolvedEntry -> m InternalEntry
check_entry normalize env mod = case mod of 
  Singleχ _ bind val -> do
    case bind of 
      OptBind (Just n, Just a) -> do
        (a_typd, a_ty) <- infer normalize env a
        a_normal <- normalize env a_ty a_typd
        val' <- check normalize env val a_normal
        pure (Singleχ () (AnnBind (n, a_normal)) val')
      OptBind (Just n, Nothing) -> do
        (val_typd, val_ty) <- infer normalize env val
        val_normal <- normalize env val_ty val_typd
        pure (Singleχ () (AnnBind (n, val_ty)) val_normal)
      OptBind (Nothing, _) -> throwError "Expecting Single definition to have a name"
    
  Mutualχ _ terms -> do
    types <- mapM check_ty terms
    let env' = foldl' (\env (n, ty) -> insert n (Nothing, ty) env) env types
    terms' <- mapM (check_term env') (zip terms (map snd types))
    pure $ Mutualχ () terms'
    where 
      check_ty (n,a,_) = do
        (a_typd, a_ty) <- infer normalize env a
        a_normal <- normalize env a_ty a_typd
        pure (n, a_normal)
      
      check_term env ((n,_,val), tipe) = do
        val' <- check normalize env val tipe
        pure (n, val', tipe)
    


-- TODO: swap environment → world?
check_module :: (Environment Name e, MonadError SigilDoc m, MonadGen m) => Evaluator m e InternalCore -> e (Maybe InternalCore, InternalCore) -> ResolvedModule -> m InternalModule
check_module normalize env mod = do
  defs' <- check_entries env (mod^.module_entries)
  pure $ set module_entries defs' mod 
  where 
    check_entries _ [] = pure []
    check_entries env (d:ds) = do
      d' <- check_entry normalize env d
      case d' of
        Mutualχ () defs -> do
          let env' = foldl' (\env (n, ty, val) -> insert n (Just val, ty) env) env defs
          ds' <- check_entries env' ds
          pure (d' : ds')
        Singleχ () (AnnBind (n, ty)) val -> do
          let env' = insert n (Just val, ty) env
          ds' <- check_entries env' ds
          pure (d' : ds')
  

-- TODO: replace with check_sub!!
check_eq :: (MonadError SigilDoc m, AlphaEq n a, Pretty a) => a -> a -> m ()
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
