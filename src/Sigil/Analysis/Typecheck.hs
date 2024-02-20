{-# LANGUAGE ScopedTypeVariables #-}
module Sigil.Analysis.Typecheck
  ( CheckInterp(..)
  , TCErr(..)
  , infer_core
  , check_core
  , check_entry
  , check_module
  , get_universe
  ) where


{-------------------------------- TYPECHECKING ---------------------------------}
{- The typechecker implemented here is in a 'bidirectional' style.             -}
{-                                                                             -}
{- Basic Overview                                                              -}
{----------------                                                              -}
{- This means that we have two functions, with approximate signatures:         -}
{- check : Env → Term → Type → Either Err Term'                                -}
{- infer : Env → Term → Either Err (Term', Type')                              -}
{-                                                                             -}
{- These two functions generally do what they say on the tin:                  -}
{- • Check will type-check a term. The type is assumed to be in normal form,   -}
{-   while the term may be unnormalized. The returned term has any missing     -}
{-   type-annotations filled in.                                               -}
{- • Infer will infer the type of a term. The returned term and type have all  -}
{-   annotations filled-in, although the type can NOT be assumed to be in      -}
{-   normal form.                                                              -}
{-                                                                             -}
{- These two functions are mutually recursive. For example, if we want to      -}
{- check that 'inc 1' has type 'Nat', then the check function will first       -}
{- need to infer the type of 'inc' as Nat → Nat before continuing with         -}
{- typechecking.                                                               -}
{-                                                                             -}
{- Likewise, if we are inferring the type of 'inc 1', then we first infer      -}
{- 'inc' as having type Nat → Nat, then check that the argument '1' has the    -}
{- type 'Nat'.                                                                 -}
{-                                                                             -}
{- Unification and Inference                                                   -}
{---------------------------                                                   -}
{- Note that the 'infer' and 'check' functions are incomplete - they neither   -}
{- fully infer or check the type of a value. There is a final step which       -}
{- happens afterwards: unification.                                            -}
{-                                                                             -}
{- Both check and infer have a third return value - a formula, which           -}
{- corresponds to constraints encountered during typechecking. They both have  -}
{- an extra return value - a formula. This formula and the process of          -}
{- unification are described in Abstract/Unify.hs and Interpret/Unify.hs,      -}
{- respectively. I will demonstrate the process with a small example below:    -}
{-                                                                             -}
{- Take the simple function 'λ x → x + x'. We will call 'infer' on this        -}
{- function. It sees that 'x' is unannodated, so it generates a formula        -}
{- with structure ∃ A : 𝕌. _. The '_' will be filled in by the formula         -}
{- generated by subsequent recursive calls to check and/or infer. We also add  -}
{- into the typechecking environment 'x : A', then recursively infer the type  -}
{- of 'x + x'. An application will traverese the LHS first, meaning we         -}
{- first infer '+' as, e.g. Nat → Nat → Nat, then progressively move on to     -}
{- typecheck the arguments (in this case just 'x' twice). When check hits      -}
{- a term like 'x' with no internal structure to traverse into, it will simply -}
{- generate an equality formula, i.e. 'check x Nat' will generate the formula  -}
{- A ≃ Nat (as it looks up the type of 'x' and discovers it to be 'A').        -}
{- Thus, the final formula is ∃ A : 𝕌. A ≃ Nat ∧ A ≃ Nat, the returned term is -}
{- 'λ x : A. x + x' and the returned type is 'Nat'. Solving the formula gives  -}
{- the substitution (A ↦ Nat), which we substitue back into the term to get    -}
{- the final term 'λ x : Nat. x + x'.                                          -}
{-                                                                             -}
{- Unification and Implicits                                                   -}
{---------------------------                                                   -}
{- TODO: Document implementation once the algorithms & strategies are          -}
{-       finalized                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Prelude hiding (lookup)
import Control.Monad (forM, unless)
import Control.Monad.Except (MonadError, throwError)
import Control.Lens
import Control.Monad.Writer.Lazy (WriterT, lift, runWriterT, tell, censor)
import Data.Foldable
import qualified Data.Set as Set

import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Unify (Formula(..), Quant(..), SingleConstraint(..))
import Sigil.Abstract.Substitution (Substitution, subst, (↦), free_vars)
import Sigil.Abstract.Environment
import Sigil.Concrete.Decorations.Implicit
import Sigil.Concrete.Resolved
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Internal

data TCErr
  = NormErr Range SigilDoc 
  | PrettyErr Range SigilDoc 
  | SolveErr Range SigilDoc

instance SigilPretty TCErr where  
  spretty tcerr = case tcerr of 
    NormErr range doc -> vsep [doc, ("at: " <+> pretty range)]
    PrettyErr range doc -> vsep [doc, ("at: " <+> pretty range)]
    SolveErr range doc -> vsep [doc, ("at: " <+> pretty range)]

data CheckInterp m err env = CheckInterp
  { normalize :: (SigilDoc -> err) -> env -> InternalCore -> InternalCore -> m InternalCore
  , αβη_eq :: (SigilDoc -> err) -> env -> InternalCore -> InternalCore -> InternalCore -> m Bool
  , solve :: (SigilDoc -> err) -> env -> InternalFormula -> m (Substitution Name InternalCore)
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
  

infer_core :: (MonadError err m, MonadGen m) => CheckInterp m err env -> Env env m -> ResolvedCore -> m (InternalCore, InternalCore)
infer_core interp@CheckInterp{..} env term = do
  ((term', ty), formula) <- runWriterT $ infer interp env term
  sub <- solve (lift_err . SolveErr (range term)) (i_impl env) formula
  let term'' = subst sub term'
      ty' = subst sub ty
  pure $ (term'', ty')

check_core :: (MonadError err m, MonadGen m) => CheckInterp m err env -> Env env m -> ResolvedCore -> InternalCore -> m InternalCore
check_core interp@CheckInterp{..} env term ty = do
  (term', formula) <- runWriterT $ check interp env term ty
  sub <- solve (lift_err . SolveErr (range term)) (i_impl env) formula
  pure $ subst sub term'

infer :: forall env err m. (MonadError err m, MonadGen m)
  => CheckInterp m err env -> Env env m -> ResolvedCore -> WriterT InternalFormula m (InternalCore, InternalCore)
infer interp@(CheckInterp {..}) env term =
  let infer' = infer interp
      check' = check interp
      normalize' env ty val = lift $ normalize (lift_err . NormErr (range term)) (i_impl env) ty val

      lookup_err' n env = do
        val <- lift $ lookup n env
        maybe (throwError' $ "Implementation Error at Analysis/Typecheck:infer can't find variable:" <+> pretty n) pure val

      throwError' :: SigilDoc -> WriterT InternalFormula m a
      throwError' = throwError . lift_err . PrettyErr (range term)
      
  in 
    case term of
      Varχ _ n -> do
        ty <- lookup_err' n env
        pure (Var n, ty)
      Uniχ _ j -> pure (Uni j, Uni (j + 1))

      Appχ (_, at) l r ->
        let (head, args) = unroll (l, [(at, r)])
            chop env mty = \case 
              [] -> do
                pure ([], mty)
              ((at, arg):args) -> case mty of 
                Prd at' (AnnBind (n, a)) b
                  | at == at' -> do
                      arg' <- check' env arg a
                      b' <- lift $ norm_ty interp (range arg) env (subst (n ↦ arg') b)
                      (_1 %~ ((at, arg'):)) <$> chop env b' args
                  | at' == Implicit -> do
                      x <- fresh_varn "#imp-in-"
                      censor (Bind Exists x a) $ do
                        env' <- lift $ insert x (Nothing, a) env
                        Var x ∈ a
                        -- TODO: do normalizing substitution here!
                        b' <- lift $ norm_ty interp (range b) env' (subst (n ↦ Var x) b)
                        (_1 %~ ((Implicit, Var x):)) <$> chop env' b' ((at, arg):args)
                  | otherwise -> throwError' "implicit application to non-implicit product"
                _ -> throwError' "TODO: chop not implemented for non-Prd mty"

            unroll ((Appχ (_, at) l r), args) = unroll (l, ((at, r):args))
            unroll (head, args) = (head, args)

            roll head [] = head
            roll head ((at, arg) : args) = roll (App at head arg) args
         in do
           (head', ty) <- infer' env head
           ty' <- lift $ norm_ty interp (range head) env ty
           (args', ret_ty) <- chop env ty' args
           pure $ (roll head' args', ret_ty)
      
      Absχ (_,at) (OptBind (mn, ma)) body -> 
        case ma of 
          Just a -> do
            (a', asort) <- infer' env a
            a_norm <- normalize' env asort a'
            
            env' <- maybe (pure env) (\n -> lift $ insert n (Nothing, a_norm) env) mn
            (body', ret_ty) <- infer' env' body
            (n,n') <- case mn of
              Just n -> if n `Set.member` free_vars ret_ty then pure (n, n) else (n,) <$> fresh_var "_"
              Nothing -> (\v -> (v,v)) <$> fresh_var "_"
            
            pure (Abs at (AnnBind (n, a')) body', Prd at (AnnBind (n', a')) ret_ty)
          Nothing -> do
            n <- case mn of
              Just n -> pure n
              Nothing -> fresh_var "_"
            ex <- fresh_varn "#inf"
            env' <- lift $ insert n (Nothing, Var ex) =<< insert ex (Nothing, Uni 0) env
            -- TODO: how to get universe level??
            censor (Bind Exists ex (Uni 0)) $ do
              (body', ret_ty) <- infer' env' body
              pure $ (Abs at (AnnBind (n, Var ex)) body', Prd at (AnnBind (n, Var ex)) ret_ty)
      
      Prdχ (_,at) (OptBind (maybe_n, Just a)) b -> do
        (a', aty) <- infer' env a
        a_norm <- normalize' env aty a'
      
        n' <- maybe (fresh_var "_") pure maybe_n
        env' <- lift $ insert n' (Nothing, a_norm) env
        (b', bty) <- infer' env' b
      
        i <- check_lvl lift_err aty
        j <- check_lvl lift_err bty
        pure (Prd at (AnnBind (n', a')) b', Uni (max i j))

      Indχ _ name (Just a) ctors -> do
        (a', asort) <- infer' env a
        anorm <- normalize' env asort a'
        env' <- lift $ insert name (Just anorm, asort) env
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

      Recχ _ (OptBind (m_rnm, m_rty)) val cases -> do
        rnm <- case m_rnm of 
          Just nm -> pure nm
          Nothing -> fresh_varn "_-"

        case m_rty of 
          Just rty -> do
            (rty', rsort) <- infer' env rty
            rnorm <- normalize' env rsort rty'
            case rnorm of
              (Prd _ (AnnBind (_, inty)) out) -> do -- TODO: use nm at
                val' <- check' env val inty
                cases' <- do
                  env' <- lift $ insert rnm (Nothing, rnorm) env
                  mapM (check_case env' out inty) cases
                pure $ (Rec (AnnBind (rnm, rty')) val' cases', out)
              _ -> throwError' "Expecting recursive function have product type"
  
          Nothing -> do
            (val', inty) <- infer' env val
            x <- fresh_varn "#ex-rec-"
            arg <- fresh_varn "#rec-arg-"
            -- TODO: universe level? (infer universes)
            censor (Bind Exists x (Uni 0)) $ do
              env' <- lift $ insert x (Nothing, Uni 0) env
              Var x ∈ Uni 0
              cases' <- do
                env'' <- lift $ insert rnm (Nothing, Prd Regular (AnnBind (arg, inty)) (Var x)) env'
                mapM (check_case env'' (Var x) inty) cases
              pure $ (Rec (AnnBind (rnm, Prd Regular (AnnBind (arg, inty)) (Var x))) val' cases', Var x)


        where
          check_case env out inty (pat, core) = do
            env' <- update_env env inty pat
            core' <- check' env' core out
            pure $ (pat, core')

          update_env :: Env env m -> InternalCore -> Pattern Name -> WriterT InternalFormula m (Env env m)
          update_env env inty = \case 
            PatVar n -> lift $ insert n (Nothing, inty) env 
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

      _ -> throwError . lift_err . PrettyErr (range term) $ vsep ["infer not implemented for resolved term:", pretty term]


check :: forall m err env. (MonadError err m, MonadGen m)
  => CheckInterp m err env -> Env env m -> ResolvedCore -> InternalCore -> WriterT InternalFormula m InternalCore
check interp@(CheckInterp {..}) env term ty =
  let infer' = infer interp
      check' = check interp
      normalize' env ty val = lift $ normalize (lift_err . NormErr (range term)) (i_impl env) ty val

      throwError' :: SigilDoc -> WriterT InternalFormula m a
      throwError' = throwError . lift_err . PrettyErr (range term)
  in
    case term of
      Uniχ _ j -> case ty of 
        Uni k
          | j < k -> pure (Uni j)
          | otherwise -> throwError' "Universe-level check failed"
        _ -> throwError' "Univserse must have universe as type"

      Absχ (_,Regular) (OptBind (Just n₁, maty)) body ->
        case ty of 
          Prd Regular (AnnBind (n₂, a₂)) ret_ty -> do
            case maty of 
              Just a₁ -> do
                (a_typd, a_kind) <- infer' env a₁
                a_normal <- normalize' env a_kind a_typd
                a_normal ≗ a₂ -- Assume a₂ is already normal
              Nothing -> pure ()
            censor (Bind Forall n₁ a₂) $ do
              ret_ty' <- if (n₁ == n₂)
                then pure ret_ty
                else lift $ norm_ty interp (range body) env (subst (n₂ ↦ Var n₁) ret_ty)
              env' <- lift $ insert n₁ (Nothing, a₂) env
              body' <- check' env' body ret_ty'
              pure $ Abs Regular (AnnBind (n₁, a₂)) body'

          -- Implicit product names are automatically instantiated
          -- For example, if we have (λ x → x) ⮜ (⟨A ⮜ 𝕌⟩ → A → A), then we automatically
          -- 'wrap' λ x → x by adding an extra implicit argument, i.e convert it
          -- to λ ⟨A⟩ → (λ x → x)
          Prd Implicit (AnnBind (n₂, a₂)) ret_ty -> do
            -- TODO: freshen n₂?
            env' <- lift $ insert n₂ (Nothing, a₂)  env
            internal <- check' env' term ret_ty
            pure $ Abs Implicit (AnnBind (n₂, a₂)) internal

    
          _ -> do
            case maty of 
              Just a₁ ->  do
                (a_typd, a_kind) <- infer' env a₁
                a_normal <- normalize' env a_kind a_typd
                e <- fresh_varn "abs-ex"
                v <- fresh_var "_"
                -- TODO: check ty is well-formed and inhabits some universe
                -- ∃ e ⮜ (a → 𝕌 n)
                lvl <- lift $ get_universe lift_err (range ty) env ty 
                censor (Bind Exists e (Prd Regular (AnnBind (v, a_normal)) (Uni lvl))) $ do
                  Prd Regular (AnnBind (n₁, a_normal)) (App Regular (Var e) (Var n₁)) ≗ ty
                  env' <- lift $ insert n₁ (Nothing, a_normal) env
                  Abs Regular (AnnBind (n₁, a_normal)) <$> check' env' body (App Regular (Var e) (Var n₁))
              Nothing -> throwError' "TODO: No type annotation for checked type!"

      Absχ (_,Implicit) (OptBind (Just n₁, maty)) body ->
        case ty of 
          Prd Implicit (AnnBind (n₂, a₂)) ret_ty -> do
            case maty of 
              Just a₁ -> do
                (a_typd, a_kind) <- infer' env a₁
                a_normal <- normalize' env a_kind a_typd
                a_normal ≗ a₂ -- Assume a₂ is already normal
              Nothing -> pure ()
            let ret_ty' = if (n₁ == n₂) then ret_ty else subst (n₂ ↦ Var n₁) ret_ty
            censor (Bind Forall n₁ a₂) $ do
              env' <- lift $ insert n₁ (Nothing, a₂) env
              body' <- check' env' body ret_ty'
              pure $ Abs Regular (AnnBind (n₁, a₂)) body'
          _ -> do
            throwError' "TODO: implicit-lambda with non-implicit type check should be implemented"
            -- e <- getNewWith "@e"
            -- tyA <- checkType b tyA tipe
            -- addToEnv (∃) e (forall "" tyA tipe) $ do
            --   forall x tyA (Spine e [var x]) ≐ ty
            --   Abs x tyA <$> addToEnv (.∀) x tyA (checkType b sp $ Spine e [var x])
    
      Prdχ (_,at) (OptBind (mn, Just a)) b -> do
        a' <- check' env a ty
        a_normal <- normalize' env ty a'
        n <- maybe (fresh_var "_") pure mn
        b' <- do { env' <- lift $ insert n (Nothing, a_normal) env; check' env' b ty }
        pure $ Prd at (AnnBind (n, a')) b'

      -- TODO: add cases for Eql and Dap
      -- TODO: make apps able to be implicit!
      Appχ (_, at) l r ->
        let (head, args) = unroll (l, [(at, r)])
            chop env mty = \case 
              [] -> do
                ty ≗ mty
                pure []
              ((at, arg):args) -> case mty of 
                Prd at' (AnnBind (n, a)) b
                  | at == at' -> do
                      arg' <- check' env arg a
                      b' <- lift $ norm_ty interp (range arg) env (subst (n ↦ arg') b)
                      ((at, arg'):) <$> chop env b' args
                  | at' == Implicit -> do
                      x <- fresh_varn "#imp-in-"
                      censor (Bind Exists x a) $ do
                        env' <- lift $ insert x (Nothing, a) env
                        Var x ∈ a
                        -- TODO: replace the subst here with a normalizing substitution
                        b' <- lift $ norm_ty interp (range b) env' (subst (n ↦ Var x) b)
                        ((Implicit, Var x):) <$> chop env' b' ((at, arg):args)
                  | otherwise -> throwError' "implicit application to non-implicit product"
                _ -> throwError' "TODO: chop not implemented for non-Prd mty"

            unroll ((Appχ (_, at) l r), args) = unroll (l, ((at, r):args))
            unroll (head, args) = (head, args)

            roll head [] = head
            roll head ((at, arg) : args) = roll (App at head arg) args
         in do
           (head', ty) <- infer' env head
           ty' <- lift $ norm_ty interp (range head) env ty
           roll head' <$> chop env ty' args

      Indχ _ n (Just a) ctors -> do
        (a', asort) <- infer' env a
        anorm <- normalize' env asort a'
        anorm ≗ ty

        env' <- lift $ insert n (Just anorm, asort) env
        ctors' <- forM ctors $ \(label, ty) -> do
          -- TODO: level check??
          --ty' <- check' env' ty asort -- TODO: is this predicativity??
          (ty', _) <- infer' env' ty
          pure $ (label, ty')
        pure $ Ind n a' ctors'
      Indχ _ _ Nothing _ -> do
        throwError' $ "Inductive datatype definition must bind recursive type (solution WIP)"
                              
      Ctrχ _ label mty -> do
        _ <- case mty of
          Just ty' -> do
            (ity, sort) <- infer' env ty'
            nty <- normalize' env sort ity
            case nty of 
              ind@(Ind n _ ctors) -> case find ((== label) . fst) ctors of
                Just (_, val) -> do
                  ty ≗ (subst (n ↦ ind) val)
                Nothing -> throwError' $ "Couln't find constructor" <+> pretty label
              _ -> throwError' $ "Constructor" <+> pretty label <+> "must be projected from inductive type"
          _ -> pure ()

        case prod_out ty of
          ind@(Ind n _ ctors) -> case find ((== label) . fst) ctors of
            Just (_, val) -> do
              ty ≗ (subst (n ↦ ind) val)
              pure $ Ctr label ty
            Nothing -> throwError' $ "Couln't find constructor" <+> pretty label
          _ -> throwError' $ "Constructor" <+> pretty label <+> "must be annotated so as to produce an inductive datatype"

      Recχ _ (OptBind (m_rnm, m_rty)) val cases -> do
        rnm <- case m_rnm of 
          Just nm -> pure nm
          Nothing -> fresh_varn "_-"

        case m_rty of 
          Just rty -> do
            (rty', rsort) <- infer' env rty
            rnorm <- normalize' env rsort rty'
            case rnorm of
              (Prd _ (AnnBind (_, inty)) out) -> do -- TODO: use nm at
                out ≗ ty
                val' <- check' env val inty
                cases' <- do
                  env' <- lift $ insert rnm (Nothing, rnorm) env
                  mapM (check_case env' out inty) cases
                pure $ Rec (AnnBind (rnm, rty')) val' cases'
              _ -> throwError' "Expecting recursive function have product type"
  
          Nothing -> do
            (val', inty) <- infer' env val
            arg <- fresh_varn "#rec-arg-"
            -- TODO: universe level? (infer universes)
            cases' <- do
              env' <- lift $ insert rnm (Nothing, Prd Regular (AnnBind (arg, inty)) ty) env
              mapM (check_case env' ty inty) cases
            pure $ Rec (AnnBind (rnm, Prd Regular (AnnBind (arg, inty)) ty)) val' cases'


        where
          check_case env out inty (pat, core) = do
            env' <- update_env env inty pat
            core' <- check' env' core out
            pure $ (pat, core')

          update_env :: Env env m -> InternalCore -> Pattern Name -> WriterT InternalFormula m (Env env m)
          update_env env inty = \case 
            PatVar n -> lift $ insert n (Nothing, inty) env 
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


      _ -> do
        (term', ty') <- infer' env term
        ty_norm <- lift $ norm_ty interp (range term) env ty'
        iterm <- implicit_cons_eq interp (range term) env ty ty_norm term'
        -- TODO: This is a temporary hack that will break if the ∃ can't be instantiated! 
        --       Should rectify/fix this later. 
        -- Suggestions: Bubble the ∃ up the hierarchy (related to ascribe?)
        pure iterm

-- Utility functions for Checking Resolved Terms, specifically for working with telescopes
infer_resolved_tel :: forall env err m. (MonadError err m, MonadGen m)
  => Range -> CheckInterp m err env -> Env env m -> ResolvedTel
  -> WriterT InternalFormula m (InternalTel, Env env m, Env env m, Env env m)
infer_resolved_tel range interp@(CheckInterp {..}) env tel =
  let infer' = infer interp
      check' = check interp
      normalize' env ty val = lift $ normalize (lift_err . NormErr range) (i_impl env) ty val
      throwError' = throwError . lift_err . PrettyErr (Range Nothing)

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

        env_l' <- lift $ insert n (Just v1_norm, ty_norm_l) env_l
        env_r' <- lift $ insert n (Just v2_norm, ty_norm_r) env_r
        env_m' <- lift $ insert n (Nothing, ty_norm_m) env_m
        infer_tel tel
          (tel_in <> [(AnnBind (n, (ty_m, v1', v2')), prf')])
          env_l' env_r' env_m'
      infer_tel _ _ _ _ _ = throwError' "Error in inferring tel: optbind not implemented"
  in infer_tel tel [] env env env

  
check_entry :: (MonadError err m, MonadGen m)
  => CheckInterp m err env -> Env env m -> ResolvedEntry -> m InternalEntry
check_entry interp@(CheckInterp {..}) env mod =
  let throwError' = throwError . lift_err . PrettyErr (Range Nothing)
  in case mod of 
    Singleχ _ bind val -> do
      case bind of 
        OptBind (Just n, Just a) -> do
          (a_typd, a_ty) <- infer_core interp env a
          a_normal <- normalize (lift_err . NormErr (range a)) (i_impl env) a_ty a_typd
          val' <- check_core interp env val a_normal
          pure (Singleχ () (AnnBind (n, a_typd)) val')
        OptBind (Just n, Nothing) -> do
          (val_typd, val_ty) <- infer_core interp env val
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
          ty' <- norm_ty interp (range ty) env ty
          val' <- eval (i_impl env) ty val
          env' <- case n of 
            Left qn -> insert_path qn (val', ty') env
            Right _ -> throwError $ lift_err $ PrettyErr (range d) "Unexpected error: Module entry bound local name." 
          ds' <- check_entries env' ds
          pure (d' : ds')
  
    eval = normalize (lift_err . NormErr (Range Nothing))

(≗) :: Monad m => InternalCore -> InternalCore -> WriterT InternalFormula m ()
l ≗ r = unless (l == r) $ tell (Conj [l :≗: r])

(∈) :: Monad m => InternalCore -> InternalCore -> WriterT InternalFormula m ()
l ∈ r = tell $ Conj [l :∈: r]

-- check_lvl :: (MonadError err m, Binding b, Pretty (Core b n χ)) => (TCErr -> err) -> Core b n χ -> m Int
check_lvl _ (Uniχ _ i) = pure i
check_lvl lift_err term@(Prdχ _ bn b) = case tipe bn of
  Just a -> max <$> check_lvl lift_err a <*> check_lvl lift_err b
  Nothing -> throwError $ lift_err $ PrettyErr (range term) ("expected 𝕌ᵢ, got:" <+> pretty term) 
check_lvl lift_err term = throwError $ lift_err $ PrettyErr (range term) ("expected 𝕌ᵢ, got:" <+> pretty term) 

prod_out :: Core b n χ -> Core b n χ
prod_out = \case 
  Prdχ _ _ r -> prod_out r
  v -> v

norm_ty :: MonadError err m => CheckInterp m err env -> Range -> Env env m -> InternalCore -> m InternalCore
norm_ty (CheckInterp {..}) range env ty = do
  lvl <- get_universe lift_err range env ty
  normalize (lift_err . NormErr range) (i_impl env) (Uni lvl) ty
  
  -- TODO: get_universe is a likely source of bugs...
get_universe :: MonadError err m => (TCErr -> err) -> Range -> Env env m -> InternalCore -> m Integer
get_universe lift_error r env = go env where
  go env = \case
    Var n -> do 
      res <- lookup n env
      case res of
        Just ty -> go env ty
        Nothing -> throwError $ lift_error $ PrettyErr r
          ( "Implementation error at Typecheck/get_universe:"
            <+> "Couldn't resolve variable:" <+> pretty n )
    
    -- Type Formers
    Uni i -> pure $ i + 1
    Prd _ (AnnBind (n, a)) b -> do
      env' <- insert n (Nothing, a) env
      max <$> go env a <*> go env' b
    Ind _ ty _ -> go env ty
    Eql _ ty _ _ -> go env ty
    
    -- Eliminators
    App _ l r -> max <$> go env l <*> go env r
    Rec (AnnBind (_, ty)) _ _ -> go env ty
    -- ETC _ -> 0
    -- CTE _ -> 0
    -- ??
    
    -- Value Terms
    Abs _ _ _ -> pure 0
    Ctr _ _ ->   pure 0
    Dap _ _ ->   pure 0
    TrR _ _ _ -> pure 0
    TrL _ _ _ -> pure 0
    -- LfR _ _ _ -> 0
    -- LfL _ _ _ -> 0

implicit_cons_eq :: (MonadGen m, MonadError err m) => (CheckInterp m err env) -> Range -> Env env m
  -> InternalCore -> InternalCore -> InternalCore -> WriterT InternalFormula m InternalCore
implicit_cons_eq interp range env ety ty val = go env ty val
  where go env ty val = case ty of
          Prd Implicit (AnnBind (n, a)) b -> do
            e <- fresh_varn "#iex-"
            censor (Bind Exists e a) $ do
              env' <- lift $ insert e (Nothing, a) env
              Var e ∈ a
              b' <- lift $ norm_ty interp range env' (subst (n ↦ Var e) b)
              go env' b' (App Implicit val (Var e))
    
          _ -> do 
            ety ≗ ty
            pure val

