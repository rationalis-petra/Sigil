module Sigil.Analysis.Typecheck
  ( Checkable(..)
  , TCErr(..)
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
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Internal

data TCErr
  = NormErr SigilDoc Range
  | PrettyErr SigilDoc Range

instance SigilPretty TCErr where  
  spretty tcerr = case tcerr of 
    NormErr doc range -> vsep [doc, ("at: " <+> pretty range)]
    PrettyErr doc range -> vsep [doc, ("at: " <+> pretty range)]

type Evaluator m err e t = (SigilDoc -> err) -> e (Maybe t,t) -> t -> t -> m t

{-------------------------------------------------------------------------------}
{- The checkable type is used to implement the bidirectional typechecking      -}
{- • For infer, the argument is a term, and the return value if is a           -}
{-   (type, term) pair.                                                        -}
{- • for check, the argument is a term and it's asserted type, and the return  -}
{-   value is a term                                                           -}
{- IMORTANT: Neither the return type nor return term are guaranteed to be in   -}
{- normal form.                                                                -}
{-------------------------------------------------------------------------------}

class Checkable n a t | a -> n t where 
  infer :: (Environment n e, MonadError err m, MonadGen m) => Evaluator m err e t -> (TCErr -> err) -> e (Maybe t,t) -> a -> m (t, t)
  check :: (Environment n e, MonadError err m, MonadGen m) => Evaluator m err e t -> (TCErr -> err) -> e (Maybe t,t) -> a -> t -> m t

instance Checkable Name InternalCore InternalCore where 
  infer normalize liftErr env term =
    let infer' = infer normalize liftErr
        check' = check normalize liftErr
        normalize' = normalize (liftErr . flip NormErr (range term))
        throwError' = throwError . liftErr . flip PrettyErr (range term)
        lookup_err' = lookup_err (liftErr . flip PrettyErr (range term))
    in 
      case term of
        Var n -> (\(_, ty) -> (term, ty)) <$> lookup_err' n env
        Uni j -> pure (term, Uni (j + 1))
        App l r -> do
          (l', lty) <- infer' env l
          (AnnBind (n, arg_ty), ret_ty) <- check_prod liftErr lty
          r' <- check' env r arg_ty
          pure (App l' r', subst (n ↦ r) ret_ty)
      
        Abs (AnnBind (n, a)) body -> do
          (a', aty) <- infer' env a
          a_norm <- normalize' env aty a'
     
          let env' = insert n (Nothing, a_norm) env
          (body', ret_ty) <- infer' env' body
     
          pure (Abs (AnnBind (n, a')) body', Prd (AnnBind (n, a')) ret_ty)
     
        Prd (AnnBind (n, a)) b -> do
          (a', aty) <- infer' env a
          a_norm <- normalize' env aty a'
     
          let env' = insert n (Nothing, a_norm) env
          (b', bty) <- infer' env' b
     
          i <- check_lvl liftErr aty
          j <- check_lvl liftErr bty
          pure (Prd (AnnBind (n, a')) b', Uni (max i j))
      
        _ -> throwError' $ "infer not implemented for term:" <+> pretty term
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check normalize liftErr env term ty =
    let infer' = infer normalize liftErr
        check' = check normalize liftErr
        throwError' = throwError . liftErr . flip PrettyErr (range term)
    in 
      case (term, ty) of
        (Uni j, Uni k)
          | j < k -> pure term
          | otherwise -> throwError' "universe-level check failed"
        
        -- TODO: generalize to more bindings; notably untyped bindings!!
        (Abs (AnnBind (n, a)) body, Prd (AnnBind (_,a')) ret_ty) -> do
          check_eq liftErr a a'
          body' <- check'(insert n (Nothing, a) env) body ret_ty
          pure $ Abs (AnnBind (n, a')) body'
        (Abs _ _, _) -> throwError' $ "expected λ-term to have Π-type, got" <+> pretty ty
        
        (Prd (AnnBind (n, a)) b, _) -> do
          a' <- check' env a ty
          b' <- check' (insert n (Nothing, a) env) b ty
          pure $ Prd (AnnBind (n, a')) b'
        
        _ -> do
          (term', ty') <- infer' env term
          _ <- check_eq liftErr ty ty'
          pure term'


instance Checkable Name ResolvedCore InternalCore where 
  infer normalize liftErr env term =
    let infer' = infer normalize liftErr
        check' = check normalize liftErr
        normalize' = normalize (liftErr . flip NormErr (range term))
        throwError' = throwError . liftErr . flip PrettyErr (range term)
        lookup_err' = lookup_err (liftErr . flip PrettyErr (range term))
        
    in 
      case term of
        Varχ _ n -> do
          ty <- snd <$> lookup_err' n env
          pure (Var n, ty)
        Uniχ _ j -> pure (Uni j, Uni (j + 1))
        Appχ _ l r -> do
          (l', lty) <- infer' env l
          (AnnBind (n, arg_ty), ret_ty) <- check_prod liftErr lty
          r' <- check' env r arg_ty
          rnorm <- normalize' env arg_ty r'
          pure (App l' r', subst (n ↦ rnorm) ret_ty)
        
        Absχ _ (OptBind (Just n, Just a)) body -> do
          (a', asort) <- infer' env a
          a_norm <- normalize' env asort a'
        
          let env' = insert n (Nothing, a_norm) env
          (body', ret_ty) <- infer' env' body
        
          pure (Abs (AnnBind (n, a')) body', Prd (AnnBind (n, a')) ret_ty)
        
        Prdχ _ (OptBind (maybe_n, Just a)) b -> do
          (a', aty) <- infer' env a
          a_norm <- normalize' env aty a'
        
          n' <- maybe (fresh_var "_") pure maybe_n
          let env' = insert n' (Nothing, a_norm) env
          (b', bty) <- infer' env' b
        
          i <- check_lvl liftErr aty
          j <- check_lvl liftErr bty
          pure (Prd (AnnBind (n', a')) b', Uni (max i j))
        _ -> throwError' $ "infer not implemented for term:" <+> pretty term
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check normalize liftErr env term ty =
    let infer' = infer normalize liftErr
        check' = check normalize liftErr
        normalize' = normalize (liftErr . flip NormErr (range term))
        throwError' = throwError . liftErr . flip PrettyErr (range term)
    in
      case (term, ty) of
        (Uniχ _ j, Uni k) 
          | j < k -> pure (Uni j)
          | otherwise -> throwError' "universe-level check failed"
      
        -- TODO: generalize to more bindings; notably untyped bindings!!
        (Absχ _ (OptBind (Just n, Just a)) body, Prd (AnnBind (_,a')) ret_ty) -> do
          (a_typd, a_ty) <- infer' env a
          a_normal <- normalize' env a_ty a_typd
          check_eq liftErr a_normal a'
          body' <- check' (insert n (Nothing, a_normal) env) body ret_ty
          pure $ Abs (AnnBind (n, a_typd)) body'
        (Absχ _ (OptBind (Just n, Nothing)) body, Prd (AnnBind (_,a')) ret_ty) -> do
          body' <- check' (insert n (Nothing, a') env) body ret_ty
          pure $ Abs (AnnBind (n, a')) body'
        (Absχ {}, _) -> throwError' $ "expected λ-term to have Π-type, got" <+> pretty ty
      
        (Prdχ _ (OptBind (Just n, Just a)) b, _) -> do
          -- TODO: normalization??
          a' <- check' env a ty
          b' <- check' (insert n (Nothing, a') env) b ty
          pure $ Prd (AnnBind (n, a')) b'
                                
        (Prdχ {}, _) -> throwError' $ "expected Π-term to have a named binding, did not!" <+> pretty term
      
        _ -> do
          (term', ty') <- infer' env term
          _ <- check_eq liftErr ty ty'
          pure term'

check_entry :: (Environment Name e, MonadError err m, MonadGen m)
  => Evaluator m err e InternalCore -> (TCErr -> err)
  -> e (Maybe InternalCore, InternalCore) -> ResolvedEntry -> m InternalEntry
check_entry normalize liftErr env mod =
  let infer' = infer normalize liftErr
      check' = check normalize liftErr
      normalize' = normalize (liftErr . flip NormErr (Range Nothing))
      throwError' = throwError . liftErr . flip PrettyErr (Range Nothing)
  in case mod of 
    Singleχ _ bind val -> do
      case bind of 
        OptBind (Just n, Just a) -> do
          (a_typd, a_ty) <- infer' env a
          a_normal <- normalize (liftErr . flip NormErr (range a)) env a_ty a_typd
          val' <- check' env val a_normal
          pure (Singleχ () (AnnBind (n, a_typd)) val')
        OptBind (Just n, Nothing) -> do
          (val_typd, val_ty) <- infer' env val
          pure (Singleχ () (AnnBind (n, val_ty)) val_typd)
        OptBind (Nothing, _) -> throwError' $ "Expecting Single definition to have a name"
      
    Mutualχ _ terms -> do
      types <- mapM check_ty terms
      let env' = foldl' (\env (n, ty) -> insert n (Nothing, ty) env) env types
      terms' <- mapM (check_term env') (zip terms (map snd types))
      pure $ Mutualχ () terms'
      where 
        check_ty (n,a,_) = do
          (a_typd, a_ty) <- infer' env a
          a_normal <- normalize' env a_ty a_typd
          pure (n, a_normal)
        
        check_term env ((n,_,val), tipe) = do
          val' <- check' env val tipe
          pure (n, val', tipe)
    


-- TODO: swap environment → world?
check_module :: (Environment Name e, MonadError err m, MonadGen m)
  => Evaluator m err e InternalCore -> (TCErr -> err)
  -> e (Maybe InternalCore, InternalCore) -> ResolvedModule -> m InternalModule
check_module normalize liftErr env mod = do
  defs' <- check_entries env (mod^.module_entries)
  pure $ set module_entries defs' mod 
  where 
    check_entries _ [] = pure []
    check_entries env (d:ds) = do
      d' <- check_entry normalize liftErr env d
      case d' of
        Mutualχ () defs -> do
          env' <- foldl' (\cmp (n, ty, val) -> do
                             env <- cmp
                             ty' <- eval_ty env ty
                             val' <- eval env ty val
                             pure $ insert n (Just val', ty') env)
                  (pure env) defs
          ds' <- check_entries env' ds
          pure (d' : ds')
        Singleχ () (AnnBind (n, ty)) val -> do
          ty' <- eval_ty env ty
          val' <- eval env ty val
          let env' = insert n (Just val', ty') env
          ds' <- check_entries env' ds
          pure (d' : ds')
  
    eval = normalize (liftErr . flip NormErr (Range Nothing))
    eval_ty env ty = do 
      (_, sort) <- infer normalize liftErr env ty   
      eval env sort ty

-- TODO: replace with check_sub!!
--check_eq _ _ = undefined
check_eq :: (MonadError err m, AlphaEq n a, Pretty a) => (TCErr -> err) -> a -> a -> m ()
check_eq liftErr ty ty'
  -- TODO: replace with αβη-equality (possibly accounted for by normalize)
  | αeq ty ty' = pure ()
  | otherwise = throwError $ liftErr $ PrettyErr ("not-equal:" <+> pretty ty <+> "and" <+> pretty ty') (Range Nothing)


-- TODO: bad for internal core?
check_prod :: (MonadError err m, Pretty (Core b n χ)) => (TCErr -> err) -> Core b n χ -> m (b n (Core b n χ), Core b n χ)
check_prod _ (Prdχ _ b ty) = pure (b, ty)
check_prod liftErr term = throwError $ liftErr $ PrettyErr ("expected prod, got:" <+> pretty term) (Range Nothing)

-- check_lvl :: (MonadError err m, Binding b, Pretty (Core b n χ)) => (TCErr -> err) -> Core b n χ -> m Int
check_lvl _ (Uniχ _ i) = pure i
check_lvl liftErr term@(Prdχ _ bn b) = case tipe bn of
  Just a -> max <$> check_lvl liftErr a <*> check_lvl liftErr b
  Nothing -> throwError $ liftErr $ PrettyErr ("expected 𝕌ᵢ, got:" <+> pretty term) (range term)
check_lvl liftErr term = throwError $ liftErr $ PrettyErr ("expected 𝕌ᵢ, got:" <+> pretty term) (range term)
