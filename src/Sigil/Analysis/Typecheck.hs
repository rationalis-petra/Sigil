{-# LANGUAGE ScopedTypeVariables #-}
module Sigil.Analysis.Typecheck
  ( Checkable(..)
  , CheckInterp(..)
  , TCErr(..)
  , check_entry
  , check_module
  , get_universe
  ) where


{-------------------------------- TYPECHECKING ---------------------------------}
{- The typechecker implemented here is a bidirectional type-checker.           -}
{- see:                                                                        -}
{-https://boxbase.org/entries/2019/jul/29/bidirectional-typechecking-dependent/-}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Prelude hiding (lookup)
import Control.Monad.Except (MonadError, throwError)
import Control.Lens
import Control.Monad (forM)
import Data.Foldable
import qualified Data.Set as Set

import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Substitution (subst, (↦), free_vars)
import Sigil.Abstract.Environment
import Sigil.Concrete.Decorations.Implicit
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

data CheckInterp m err env = CheckInterp
  { normalize :: (SigilDoc -> err) -> env -> InternalCore -> InternalCore -> m InternalCore
  , αβη_eq :: (SigilDoc -> err) -> env -> InternalCore -> InternalCore -> InternalCore -> m Bool
  , lift_err :: TCErr -> err
  }

{-------------------------------------------------------------------------------}
{- The checkable type is used to implement the bidirectional typechecking.     -}
{- Because we try and implement 'proper' type inference, infer/check also      -}
{- return a list of variables that are existentially qualified for unification -}
{- • For infer, the argument is a term, and the return value if is a           -}
{-   (type, term) pair.                                                        -}
{- • for check, the argument is a term and it's asserted type, and the return  -}
{-   value is a term                                                           -}
{- IMORTANT: Neither the return type nor return term are guaranteed to be in   -}
{- normal form.                                                                -}
{-------------------------------------------------------------------------------}
  

class Checkable a where 
  infer :: (MonadError err m, MonadGen m) => CheckInterp m err env -> Env env m -> a -> m (InternalCore, InternalCore) -- ,[n]
  check :: (MonadError err m, MonadGen m) => CheckInterp m err env -> Env env m -> a -> InternalCore -> m InternalCore -- ,[n]


instance Checkable ResolvedCore where 
  infer :: forall env err m. (MonadError err m, MonadGen m)
    => CheckInterp m err env -> Env env m -> ResolvedCore -> m (InternalCore, InternalCore)
  infer interp@(CheckInterp {..}) env term =
    let infer' = infer interp
        check' = check interp
        normalize' env = normalize (lift_err . flip NormErr (range term)) (i_impl env)

        lookup_err' n env = do
          val <- lookup n env
          maybe (throwError' $ "Implementation Error at Analysis/Typecheck:infer can't find variable:" <+> pretty n) pure val

        throwError' :: SigilDoc -> m a
        throwError' = throwError . lift_err . flip PrettyErr (range term)
        
    in 
      case term of
        Varχ _ n -> do
          ty <- lookup_err' n env
          pure (Var n, ty)
        Uniχ _ j -> pure (Uni j, Uni (j + 1))
        Appχ _ l r -> do
          (l', lty) <- infer' env l
          (AnnBind (n, arg_ty), ret_ty) <- check_prod lift_err lty
          r' <- check' env r arg_ty
          rnorm <- normalize' env arg_ty r'
          pure (App l' r', subst (n ↦ rnorm) ret_ty)
        
        Absχ (_,at) (OptBind (mn, Just a)) body -> do
          (a', asort) <- infer' env a
          a_norm <- normalize' env asort a'
        
          env' <- maybe (pure env) (\n -> insert n (Nothing, a_norm) env) mn
          (body', ret_ty) <- infer' env' body
          (n,n') <- case mn of
            Just n -> if n `Set.member` free_vars ret_ty then pure (n, n) else (n,) <$> fresh_var "_"
            Nothing -> (\v -> (v,v)) <$> fresh_var "_"
        
          pure (Abs at (AnnBind (n, a')) body', Prd at (AnnBind (n', a')) ret_ty)
        
        Prdχ (_,at) (OptBind (maybe_n, Just a)) b -> do
          (a', aty) <- infer' env a
          a_norm <- normalize' env aty a'
        
          n' <- maybe (fresh_var "_") pure maybe_n
          env' <- insert n' (Nothing, a_norm) env
          (b', bty) <- infer' env' b
        
          i <- check_lvl lift_err aty
          j <- check_lvl lift_err bty
          pure (Prd at (AnnBind (n', a')) b', Uni (max i j))

        Indχ _ name (Just a) ctors -> do
          (a', asort) <- infer' env a
          anorm <- normalize' env asort a'
          env' <- insert name (Just anorm, asort) env
          ctors' <- forM ctors $ \(label, ty) -> do
            -- TODO: level check
            -- ty' <- check' env' ty asort -- TODO: is this predicativity??
            (ty', _) <- infer' env' ty
            pure $ (label, ty')
          pure $ (Ind name a' ctors', a')
        Indχ _ _ Nothing _ -> throwError' "inductive definition should provide sort"

        Ctrχ _ label mty ->
          case mty of  
            Just ty -> do
              (ty', sort) <- infer' env ty
              nty <- normalize' env sort ty'
              case nty of
                ind@(Ind n _ ctors) -> case find ((== label) . fst) ctors of
                  Just (_, val) -> do
                    pure $ (Ctr label ty', (subst (n ↦ ind) val))
                  Nothing -> throwError' $ "Couln't find constructor" <+> pretty label
                _ -> throwError' "Constructor must be annotated so as to produce an inductive datatype"
            Nothing ->
              throwError' $ "Constructor" <+> pretty label <+> "was not provided a type"

        Recχ _ (OptBind (Just rnm, Just rty)) val cases -> do
          (rty', rsort) <- infer' env rty
          rnorm <- normalize' env rsort rty'
          (_, inty, out) <- case rnorm of
            (Prd _ (AnnBind (nm, inty)) out) -> pure (nm, inty, out)
            _ -> throwError' "Expecting recursive function have product type"
          val' <- check' env val inty

          let check_case env inty (pat, core) = do
                env' <- update_env env inty pat
                core' <- check' env' core out
                pure $ (pat, core')

              update_env :: Env env m -> InternalCore -> Pattern Name -> m (Env env m)
              update_env env inty = \case 
                PatVar n -> insert n (Nothing, inty) env 
                PatCtr label subpatterns -> do
                  -- TODO: what about dependently-typed induction!
                  args <- get_args label inty 
                  if (length args /= length subpatterns) then throwError' "Error: malformed pattern (bad number of arguments)" else pure ()
                  foldl (\m (inty, subpat) -> m >>= \env -> update_env env inty subpat) (pure env) (zip args subpatterns)

              get_args label ty@(Ind rn _ ctors) = do
                case find ((== label) . fst) ctors of 
                  Just (_, cty) -> 
                    let cty' = subst (rn ↦ ty) cty
                        pargs (Prd Regular (AnnBind (_, a)) b) = [a] <> pargs b
                        pargs (Prd Implicit (AnnBind (_, a)) b) = [a] <> pargs b
                        pargs _ = []
                    in pure $ pargs cty'
                  Nothing -> throwError' "Failed to find label for recursion"
              get_args _ _ = throwError' "Can't pattern match on non-inductive type"

          cases' <- do
            env' <- (insert rnm (Nothing, rnorm) env)
            mapM (check_case env' inty) cases
          pure $ (Rec (AnnBind (rnm, rty')) val' cases', out)

        Dapχ _ tel val -> do  
          (tel', env_l, env_r, env_m) <- infer_resolved_tel (range term) interp env tel
          (val_l, _) <- infer' env_l val
          (val_r, _) <- infer' env_r val
          (val_neu, ty_neu) <- infer' env_m val
          pure (Dap tel' val_neu, Eql tel' ty_neu val_l val_r)

        Eqlχ _ tel ty v1 v2 -> do
          (tel', env_l, env_r, env_m) <- infer_resolved_tel (range term) interp env tel

          (ty_l, kind_l) <- infer' env_l ty
          (ty_r, kind_r) <- infer' env_r ty
          (ty_m, kind_m) <- infer' env_m ty
          ty_norm_l <- normalize' env_l kind_l ty_l
          ty_norm_r <- normalize' env_r kind_r ty_r
          v1' <- check' env_l v1 ty_norm_l
          v2' <- check' env_r v2 ty_norm_r
          pure (Eql tel' ty_m v1' v2', kind_m)

        TrLχ _ tel ty v -> do
          (tel', env_l, env_r, env_m) <- infer_resolved_tel (range term) interp env tel
          (ty_l, _) <- infer' env_l ty
          (ty_r, kind_r) <- infer' env_r ty
          (ty_m, _) <- infer' env_m ty
          ty_norm_r <- normalize' env_r kind_r ty_r
          v' <- check' env_r v ty_norm_r
          -- step1: check that 
          pure (TrL tel' ty_m v', ty_l)
          
        TrRχ _ tel ty v -> do
          (tel', env_l, env_r, env_m) <- infer_resolved_tel (range term) interp env tel
          (ty_l, kind_l) <- infer' env_l ty
          (ty_r, _) <- infer' env_r ty
          (ty_m, _) <- infer' env_m ty
          ty_norm_l <- normalize' env_l kind_l ty_l
          v' <- check' env_l v ty_norm_l
          pure (TrR tel' ty_m v', ty_r)

        _ -> throwError . lift_err . flip PrettyErr (range term) $ vsep ["infer not implemented for resolved term:", pretty term]
  
  
  -- Note: types are expected to be in normal form
  -- Note: environment is expected to contain types of terms!!
  check :: forall m err env. (MonadError err m, MonadGen m)
    => CheckInterp m err env -> Env env m -> ResolvedCore -> InternalCore -> m InternalCore
  check interp@(CheckInterp {..}) env term ty =
    let infer' = infer interp
        check' = check interp
        normalize' env = normalize (lift_err . flip NormErr (range term)) (i_impl env)

        throwError' :: SigilDoc -> m a
        throwError' = throwError . lift_err . flip PrettyErr (range term)
    in
      case (term, ty) of
        (Uniχ _ j, Uni k) 
          | j < k -> pure (Uni j)
          | otherwise -> throwError' "universe-level check failed"
      
        (Absχ (_,at₁) (OptBind (Just n₁, Just a₁)) body, Prd at₂ (AnnBind (n₂, a₂)) ret_ty)
          | at₁ == at₂ -> do
              (a_typd, a_kind) <- infer' env a₁
              a_normal <- normalize' env a_kind a_typd
              check_eq (range term) interp env a_kind a_typd a₂
              let ret_ty' = if (n₁ == n₂) then ret_ty else subst (n₂ ↦ Var n₁) ret_ty
              body' <- do { env' <- (insert n₁ (Nothing, a_normal) env); check' env' body ret_ty' }
              pure $ Abs at₁ (AnnBind (n₁, a_typd)) body'

          -- Do we want to do this??
          -- | at₁ == Regular -> do
          --     (a_typd, a_kind) <- infer' env a₁
          --     a_normal <- normalize' env a_kind a_typd
          --     n'₂ <- freshen n₂
          --     let fnc_ty = subst (n₂ ↦ Var n'₂) ret_ty
          --     fnc' <- check' (insert n'₂ (Nothing, a_normal) env) term fnc_ty
              
          --     pure $ Abs at₂ (AnnBind (n'₂, a₂)) fnc'
          | otherwise -> throwError' "Implicit/Regular argument type mismatch in inference"
        

        (Absχ (_,at₁) (OptBind (Just n₁, Nothing)) body, Prd at₂ (AnnBind (n₂, a)) ret_ty)
          | at₁ == at₂ -> do
              let ret_ty' = if (n₁ == n₂) then ret_ty else subst (n₂ ↦ Var n₁) ret_ty
              body' <- do { env' <- (insert n₁ (Nothing, a) env); check' env' body ret_ty' }
              pure $ Abs at₁ (AnnBind (n₁, a)) body'
          -- | at₁ == Regular -> do
          --     n'₂ <- freshen n₂
          --     let fnc_ty = subst (n₂ ↦ Var n'₂) ret_ty
          --     fnc' <- check' (insert n'₂ (Nothing, a) env) term fnc_ty
              
          --     pure $ Abs at₂ (AnnBind (n'₂, a)) fnc'
          | otherwise -> throwError' "Implicit/Regular argument type mismatch in inference"

        (Absχ {}, _) -> throwError' $ "expected λ-term to have Π-type, got" <+> pretty ty
      
        (Prdχ (_,at) (OptBind (mn, Just a)) b, _) -> do
          a' <- check' env a ty
          a_normal <- normalize' env ty a'
          n <- maybe (fresh_var "_") pure mn
          b' <- do { env' <- (insert n (Nothing, a_normal) env); check' env' b ty }
          pure $ Prd at (AnnBind (n, a')) b'

  
        (Indχ _ n (Just a) ctors, ty) -> do
          (a', asort) <- infer' env a
          check_eq (range term) interp env asort a' ty
          anorm <- normalize' env asort a'
          env' <- insert n (Just anorm, asort) env
          ctors' <- forM ctors $ \(label, ty) -> do
            -- TODO: level check??
            --ty' <- check' env' ty asort -- TODO: is this predicativity??
            (ty', _) <- infer' env' ty
            pure $ (label, ty')
          pure $ Ind n a' ctors'
        (Indχ _ _ Nothing _, _) -> do
          throwError' $ "Inductive datatype definition must bind recursive type (solution WIP)"
                                
        (Ctrχ _ label mty, ty) -> do
          _ <- case mty of
            Just ty' -> do
              (ity, sort) <- infer' env ty'
              nty <- normalize' env sort ity
              case nty of 
                ind@(Ind n sort ctors) -> case find ((== label) . fst) ctors of
                  Just (_, val) -> do
                    check_eq (range term) interp env sort ty (subst (n ↦ ind) val)
                  Nothing -> throwError' $ "Couln't find constructor" <+> pretty label
                _ -> throwError' $ "Constructor" <+> pretty label <+> "must be projected from inductive type"
            _ -> pure ()

          case prod_out ty of
            ind@(Ind n sort ctors) -> case find ((== label) . fst) ctors of
              Just (_, val) -> do
                check_eq (range term) interp env sort ty (subst (n ↦ ind) val)
                pure $ Ctr label ty
              Nothing -> throwError' $ "Couln't find constructor" <+> pretty label
            _ -> throwError' $ "Constructor" <+> pretty label <+> "must be annotated so as to produce an inductive datatype"
        -- TODO: add cases for Eql and Dap
        _ -> do
          (term', ty') <- infer' env term
          n <- get_universe lift_err (range ty) env ty
          _ <- check_eq (range term) interp env (Uni n) ty ty'
          pure term'

-- Utility functions for Checking Resolved Terms, specifically for working with telescopes

-- infer :: forall e err m. (MonadError err m, MonadGen m)
--   => CheckInterp m err e InternalCore -> e (Maybe InternalCore,InternalCore) -> ResolvedCore -> m (InternalCore, InternalCore)
infer_resolved_tel :: forall env err m. (MonadError err m, MonadGen m)
  => Range -> CheckInterp m err env -> Env env m -> ResolvedTel
  -> m (InternalTel, Env env m, Env env m, Env env m)
infer_resolved_tel range interp@(CheckInterp {..}) env tel =
  let infer' = infer interp
      check' = check interp
      normalize' env = normalize (lift_err . flip NormErr range) (i_impl env)
      throwError' = throwError . lift_err . flip PrettyErr (Range Nothing)

      infer_tel [] tel_in env_l env_r env_m = pure (tel_in, env_l, env_r, env_m) 
      infer_tel ((OptBind (Just n, Just (ty, v1, v2)), prf) : tel) tel_in env_l env_r env_m = do
        (ty_l, kind_l) <- infer' env_l ty
        (ty_r, kind_r) <- infer' env_r ty
        (ty_m, kind_m) <- infer' env_m ty

        v1' <- check' env_l v1 ty_l
        v2' <- check' env_r v2 ty_r

        prf' <- check' env prf (Eql tel_in ty_m v1' v2')

        ty_norm_l <- normalize' env_l kind_l ty_l 
        ty_norm_r <- normalize' env_r kind_r ty_r
        ty_norm_m <- normalize' env_m kind_m ty_m

        v1_norm <- normalize' env_l ty_norm_l v1'
        v2_norm <- normalize' env_r ty_norm_r v2'

        env_l' <- insert n (Just v1_norm, ty_norm_l) env_l
        env_r' <- insert n (Just v2_norm, ty_norm_r) env_r
        env_m' <- insert n (Nothing, ty_norm_m) env_m
        infer_tel tel
          (tel_in <> [(AnnBind (n, (ty_m, v1', v2')), prf')])
          env_l' env_r' env_m'
      infer_tel _ _ _ _ _ = throwError' "Error in inferring tel: optbind not implemented"
      -- infer_tel ((OptBind (Just n, Just (ty, v1, v2)), prf) : tel) tel_in env_l env_r env_m = 
      --   (prfl, kind_l) <- infer' env_l ty
      --   (ty_r, kind_r) <- infer' env_r ty
      --   (ty_m, kind_m) <- infer' env_m ty
  in infer_tel tel [] env env env

-- check_resolved_tel ::
-- check_resolved_tel = 

  

check_entry :: (MonadError err m, MonadGen m)
  => CheckInterp m err env -> Env env m -> ResolvedEntry -> m InternalEntry
check_entry interp@(CheckInterp {..}) env mod =
  let infer' = infer interp
      check' = check interp
      throwError' = throwError . lift_err . flip PrettyErr (Range Nothing)
  in case mod of 
    Singleχ _ bind val -> do
      case bind of 
        OptBind (Just n, Just a) -> do
          (a_typd, a_ty) <- infer' env a
          a_normal <- normalize (lift_err . flip NormErr (range a)) (i_impl env) a_ty a_typd
          val' <- check' env val a_normal
          pure (Singleχ () (AnnBind (n, a_typd)) val')
        OptBind (Just n, Nothing) -> do
          (val_typd, val_ty) <- infer' env val
          pure (Singleχ () (AnnBind (n, val_ty)) val_typd)
        OptBind (Nothing, _) -> throwError' $ "Expecting Single definition to have a name"


check_module :: (MonadError err m, MonadGen m)
  => CheckInterp m err env -> Env env m -> ResolvedModule -> m InternalModule
check_module interp@(CheckInterp {..}) env mod = do
  defs' <- check_entries env (mod^.module_entries)
  pure $ set module_entries defs' mod 
  where 
    check_entries _ [] = pure []
    check_entries env (d:ds) = do
      d' <- check_entry interp env d
      case d' of
        Singleχ () (AnnBind (Name n, ty)) val -> do
          ty' <- eval_ty env ty
          val' <- eval (i_impl env) ty val
          env' <- case n of 
            Left qn -> insert_path qn (val', ty') env
            Right _ -> throwError $ lift_err $ PrettyErr "Unexpected error: Module entry bound local name." (range d)
          ds' <- check_entries env' ds
          pure (d' : ds')
  
    eval = normalize (lift_err . flip NormErr (Range Nothing))
    eval_ty env ty = do 
      n <- get_universe lift_err (range ty) env ty
      eval (i_impl env) (Uni n) ty

-- TODO: replace with check_sub (?)
--check_eq _ _ = undefined
check_eq :: (MonadError err m) => Range -> (CheckInterp m err env) -> Env env m -> InternalCore -> InternalCore -> InternalCore -> m ()
check_eq range (CheckInterp {..}) env ty l r = 
  αβη_eq (lift_err . flip NormErr range) (i_impl env) ty l r >>= \case
    True -> pure ()
    False -> throwError $ lift_err $ PrettyErr ("not-equal:" <+> pretty l <+> "and" <+> pretty r) range

-- TODO: bad for internal core?
-- TODO: implicit vs explicit products
check_prod :: (MonadError err m, Pretty (Core b n χ)) => (TCErr -> err) -> Core b n χ -> m (b n (Core b n χ), Core b n χ)
check_prod _ (Prdχ _ b ty) = pure (b, ty)
check_prod lift_err term = throwError $ lift_err $ PrettyErr ("expected prod, got:" <+> pretty term) (Range Nothing)

-- check_lvl :: (MonadError err m, Binding b, Pretty (Core b n χ)) => (TCErr -> err) -> Core b n χ -> m Int
check_lvl _ (Uniχ _ i) = pure i
check_lvl lift_err term@(Prdχ _ bn b) = case tipe bn of
  Just a -> max <$> check_lvl lift_err a <*> check_lvl lift_err b
  Nothing -> throwError $ lift_err $ PrettyErr ("expected 𝕌ᵢ, got:" <+> pretty term) (range term)
check_lvl lift_err term = throwError $ lift_err $ PrettyErr ("expected 𝕌ᵢ, got:" <+> pretty term) (range term)

prod_out :: Core b n χ -> Core b n χ
prod_out = \case 
  Prdχ _ _ r -> prod_out r
  v -> v

  -- TODO: get_universe is a likely source of bugs...
get_universe :: MonadError err m => (TCErr -> err) -> Range -> Env env m -> InternalCore -> m Integer
get_universe lift_error r env = go env where
  go env = \case
    Var n -> do 
      res <- lookup n env
      case res of
        Just ty -> go env ty
        Nothing -> throwError $ lift_error $ PrettyErr
          ( "Implementation error at Typecheck/get_universe:"
            <+> "Couldn't resolve variable:" <+> pretty n ) r
    
    -- Type Formers
    Uni i -> pure $ i + 1
    Prd _ (AnnBind (n, a)) b -> do
      env' <- insert n (Nothing, a) env
      max <$> go env a <*> go env' b
    Ind _ ty _ -> go env ty
    Eql _ ty _ _ -> go env ty
    
    -- Eliminators
    App l r -> max <$> go env l <*> go env r
    Rec (AnnBind (_, ty)) _ _ -> go env ty
    -- ETC _ -> 0
    -- CTE _ -> 0
    -- ??
    TyCon ty _ _ -> go env ty
    
    -- Value Terms
    Abs _ _ _ -> pure 0
    Ctr _ _ ->   pure 0
    Dap _ _ ->   pure 0
    TrR _ _ _ -> pure 0
    TrL _ _ _ -> pure 0
    -- LfR _ _ _ -> 0
    -- LfL _ _ _ -> 0

-- Helpers for constructing the 1-1-Correspondence type
-- sigma :: Binding b => Core b n χ -> n -> Core b n χ -> Core b n χ -> Core b n χ
-- sigma u nm a b = Indχ ? 

-- is_contr :: (MonadGen m, Binding b) => Core b n χ -> Core b n χ
-- is_contr uni val = do
--   var <- fresh_var 
--   sigma (Idχ _ )

-- -- 
-- -- Given a type (in universe 𝕌)
-- correspondence :: (MonadGen m, Binding b) => Core b n χ -> Core b n χ -> Core b n χ
-- correspondence 

-- -- Make a pair at Σ-type
-- pr :: Binding b => Core b n χ -> Core b n χ -> Core b n χ -> Core b n χ
-- pr ty x y = Appχ (Appχ (Ctrχ _ "," ty) x) y


