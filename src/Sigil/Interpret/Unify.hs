{-# LANGUAGE ScopedTypeVariables, InstanceSigs #-}
--{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Interpret.Unify
  -- Exports: Unify instnace for InternalCore
  ( solve ) where


{--------------------------------- UNIFICATION ---------------------------------}
{- This file contains a Higher Order Unification Algorithm for the Sigil.       -}
{- language. As this procedure is quite complex, it may be hard to navigate    -}
{- this file. This comment contains a high-level Overview of unification, as   -}
{- well as a 'table of contents' indicating where some subcomponents are       -}
{- located (this is a big file!)                                               -}
{-                                                                             -}
{- Unification, as implemented here, is the solution of a Formula - a term     -}
{- describing a particular unification problem. This is more general than      -}
{- Formulas are defined by the structure:                                      -}
{-                                                                             -}
{-      F ≜ F ∧ F | ∀x:A. F | ∃x:A. F | A ≗ A | A ∈ A | ⊤                      -}
{-                                                                             -}
{- Where A stands for a term/type in the calculus in question, and ≗ is taken  -}
{- to mean βηα-equivalence, while A ∈ B is taken to mean 'A inhabits type B'.  -}
{-                                                                             -}
{- Note that the 'standard' unification procedure (unify two terms, M and N)   -}
{- can be emulated in this formulation of the problem with the formula         -}
{- ∃x₁:A₁. … ∃xₙ:Aₙ. M ≗ N, where the xᵢ are simply all of the free            -}
{- metavariables in M and N.                                                   -}
{-                                                                             -}
{- Further, the ∈ term can act as a generalisation of type inference/checking  -}
{- and proof search:                                                           -}
{- • M ∈ N (no free vars) is equivalent to type-checking M : N                 -}
{- • ∃n:ℕ∃. T:𝕌 n. M ∈ T is equivalent to inferring the type of M              -}
{- • ∃x:A. x∈A is like a proof search for proposition A.                       -}
{-                                                                             -}
{- The 'solve' function (which solves formulas) works by applying a series of  -}
{- meaning-preserving transformations F ⇒ F' → … → S, where S is a formula in  -}
{- solved form, which is defined:                                              -}
{-                                                                             -}
{-                   S ≜ ⊤ | S ∧ S' | ∃x. x ≗ u  ∧ S                           -}
{-                                                                             -}
{- Importantly, all equivalences (≗) in solved form are easily decidable, as   -}
{- one side is simply a variable.                                              -}
{-                                                                             -}
{------------------------------- FILE STRUCTURE --------------------------------}
{-                                                                             -}
{- The file is structured as follows:                                          -}
{- • First, relevant types are defined, including the Unifiable typeclass,     -}
{-   the Formula type and the Unification Monad                                -}
{- • The Toplevel Unification (solve) function, along with a set of helper     -}
{-   functions it uses.                                                        -}
{- • A Higher Order Unification Algorithm for Equality Constraints             -}
{- • A Higher Order Unification algorithm for Occupation Constraints           -}
{- • Common instances for the several types (pretty, eq, etc.)                 -}
{-------------------------------------------------------------------------------}


import Control.Monad (forM)
import Control.Monad.Except (MonadError, throwError)
-- import Control.Monad.Reader (MonadReader)
import Control.Lens (_1, _2, makeLenses, (^.), (%~), view)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.List as List

import Prettyprinter

import Sigil.Abstract.Unify
import Sigil.Abstract.AlphaEq
import Sigil.Abstract.Environment
import Sigil.Abstract.Substitution

import Sigil.Concrete.Internal
--import Sigil.Interpret.Term


{----------------------------- INTERNAL DATATYPES ------------------------------}
{- TODO: Unification Monad, env and Binds                                      -}
{-                                                                             -}
{- These types are for the most part direct translations of types mentioned    -}
{- above, with the exception of the 'FlatFormula' type. This exists because    -}
{- Part of the solution process involves taking an arbitrary formula and       -}
{- converting it to the form:                                                  -}
{-                                                                             -}
{-      (∃/∀)x₁:A₁…(∃/∀)xₙ:Aₙ. (F₁ ≗/∈ G₁) ∧ … ∧ (Fₖ ≗/∈ Gₖ)                   -}
{-                                                                             -}
{- This is a 'flat' formula, and is easier to solve than an arbitrary formula. -}
{-                                                                             -}
{- The procedure will then attempt to simplify a formula, by performing        -}
{- successive transformations to either discover the formula is false (⊥)      -}
{- or convert it to solved form (see Unification). These transformations can   -}
{- be broken down into three steps:                                            -}
{- • Introduce some new variable bindings (∃/∀)                                -}
{- • Substitute some existing variable(s), e.g. x for some term involving      -}
{-   these new variables                                                       -}
{- • Remove any such variables x from the bindings that have now been          -}
{-   substituted away.                                                         -}
{- While some transformations lack one of the above steps, this general        -}
{- procedure is encapsulated in the UnifyResult type. UnifyResult              -}
{- contains three members:                                                     -}
{- • A new set of bindings to use                                              -}
{- • A substitution to apply.                                                  -}
{- • A list of new constraints to add.                                         -}
{-------------------------------------------------------------------------------}


-- type Unify ann v = ReaderT (Env v) (Except (Doc ann))

-- Bindings: a value is either bound within a formula (and hence quantified)
type Binds a = [(FBind a)]

type ContT a m c = ((c -> m a) -> m a)

type UnifyResult a =
  Maybe ( Binds a
        , Substitution a
        , [SingleConstraint a])

data FlatFormula a = FlatFormula
  { _binds :: Binds a
  , _constraints :: [SingleConstraint a]
  }

data FBind a = FBind
  { _elem_quant :: Quant
  , _elem_name :: Name
  , _elem_type :: a
  }

data Atom = AVar Name | AUni Int
  deriving Eq

type Binds'            = Binds InternalCore
type FBind'            = FBind InternalCore
type Formula'          = Formula InternalCore
type UnifyResult'      = UnifyResult InternalCore
--type FlatFormula'      = Formula (Core AnnBind Name χ)
type Substitution'     = Substitution InternalCore
type SingleConstraint' = SingleConstraint InternalCore

makeLenses ''FlatFormula
makeLenses ''FBind

instance Eq (FBind a) where
  b == b' = b^.elem_name == b'^.elem_name

instance (Subst Name s a) => Subst Name s (FBind a) where
  substitute shadow sub (FBind quant name ty) = 
    FBind quant name (substitute (Set.insert name shadow) sub ty) 

  free_vars (FBind _ nm et) = Set.delete nm $ free_vars et 
    
instance (Subst Name s a) => Subst Name s (FlatFormula a) where
  substitute shadow sub (FlatFormula binds constraints) = 
    let (shadow', binds') = foldr (\ b (s, bs) ->
                                     ( Set.insert (b^.elem_name) s
                                     , substitute s sub b : bs)) (shadow, []) binds
    in FlatFormula binds' (substitute shadow' sub constraints)

  free_vars (FlatFormula binds constraints) =
    Set.difference
      (Set.fromList $ fmap (view elem_name) binds)
      (foldl Set.union Set.empty $ fmap free_vars constraints)

instance Semigroup (FlatFormula a) where
  f1 <> f2 = FlatFormula bs scons where
    bs = f1^.binds <> f2^.binds
    scons = f1^.constraints <> f2^.constraints
    
instance Monoid (FlatFormula a) where
  mempty = FlatFormula [] []

instance Pretty Atom where 
  pretty (AVar v) = pretty v
  pretty (AUni v) = pretty ((Uni v) :: InternalCore)

{---------------------------- TOP-LEVEL UNIFICATION ----------------------------}
{- The solve function is the top-level procedure, and the driver is the        -}
{- uni_while function. This will perform successive transformations until a    -}
{- formula is in 'solved form'                                                 -}
{-------------------------------------------------------------------------------}


solve :: forall ann m. (MonadError (Doc ann) m, MonadGen m) => Formula' -> m Substitution'
solve = fmap fst . (\v -> uni_while (v^.binds) mempty (v^.constraints)) . flatten where

  uni_while :: Binds' -> Substitution' -> [SingleConstraint'] -> m (Substitution', [SingleConstraint'])
  uni_while quant_vars sub cs = 
    let -- uni_with :: (MonadError (Doc ann) m, MonadReader (Env' χ) m) => (SingleConstraint' χ -> ContT b m (UnifyResult' χ))
        --   -> (Substitution' χ, [SingleConstraint' χ]) -> m (Substitution' χ, [SingleConstraint' χ])
        uni_with f backup = search_in cs []
          where
            search_in :: [SingleConstraint'] -> [SingleConstraint'] -> m (Substitution', [SingleConstraint'])
            search_in [] _ = finish Nothing
            search_in (next:rest) resolved = 
              f quant_vars next $ \case
                -- search through single constriants until we find one that
                -- updates the formula
                Just (new_fctx, sub', next) ->
                  let
                    formula  = FlatFormula new_fctx (reverse resolved <> next <> rest)
                    formula' = subst sub' formula
                  in finish $ Just (sub', formula'^.constraints, formula'^.binds)
                Nothing -> search_in rest (next:resolved)

            finish :: Maybe (Substitution', [SingleConstraint'], Binds') -> m (Substitution', [SingleConstraint'])
            finish Nothing = backup
            finish (Just (sub', cs', binds)) =
              let sub'' = sub <> sub' in
                          -- TODO: hmmmm
                uni_while (subst sub' binds) sub'' cs'
    in uni_with unify_one
      $ uni_with unify_search
      $ uni_with unify_search_atom
      $ check_finished cs >> pure (sub, cs)


  check_finished [] = pure ()
  check_finished cs = throwError ("ambiguous constraints: " <> pretty cs)

  unify_one :: Binds' -> SingleConstraint' -> ContT r m UnifyResult'
  unify_one binds constraint cont = case constraint of 
    a :≗: b -> do
      c' <- unify_eq binds a b
      case c' of 
        Nothing -> cont =<< unify_eq binds b a
        r -> cont r
    _ -> cont Nothing
  
  unify_search :: Binds' -> SingleConstraint' -> ContT r m UnifyResult'
  --unify_search binds constraint cont = case constraint of
  unify_search _ constraint cont = case constraint of
    --a :∈: b | not_higher_universe b -> right_search binds a b $ new_cont cont
    _ -> cont Nothing
    -- where 
    --   not_higher_universe (Uni _ k) = k < 1
    --   not_higher_universe _ = True
  
  unify_search_atom :: Binds' ->  SingleConstraint' -> ContT r m UnifyResult'
  --unify_search_atom binds constraint cont = case constraint of
  unify_search_atom _ constraint cont = case constraint of
    --a :∈: b -> right_search binds a b $ new_cont cont
    _ -> cont Nothing
  
  --new_cont cont constraint = cont $ fmap (\v -> (mempty, v, False)) constraint
      

{---------------------------- UNIFYING FOR EQUALITY ----------------------------}
{- The unify_eq function is for unifying constraints of the form M ≗ N.        -}
{- The procedure closely resembles Huet's Algorithm, modified to deal with     -}
{- differently quantified variables.                                           -}
{-                                                                             -}
{- The specific paper this algorithm is based off is its' description in       -}
{- "Logic Programming and Type Inference In The Calculus of Constructions"     -}
{- by Matthey Mirmann.  however, what is in my opinion a better description is -}
{- given in the papers                                                         -}
{- "Unification and Anti-Unification in the Calculus of Constructions"         -}
{- or, for a a more concise description:                                       -}
{- "Logic Programming in the LF Logical Framework"                             -}
{- both by Frank Pfenning. It is recommended you read at least one of these to -}
{- understand the code here.                                                   -}
{-------------------------------------------------------------------------------}


unify_eq :: forall m ann. (MonadError (Doc ann) m, MonadGen m) =>
  Binds' -> InternalCore -> InternalCore -> m UnifyResult'
unify_eq quant_vars a b = case (a, b) of 
  -- (Coreχ χ, Coreχ χ') ->
  --   if χ == χ' then
  --     pure $ Just (quant_vars, mempty, [])
  --   else
  --     throwError ("unequal Coreχ values" :: Doc ann)
  (Uni n, Uni n') ->
    if n == n' then
      pure $ Just (quant_vars, mempty, [])
    else
      throwError ("unequal universes:"
                  <+> "(𝕌 " <> pretty n <> ")"
                  <+> "and"
                  <+> "(𝕌 " <> pretty n' <> ")")

  (s, s') | αeq s s' -> pure $ Just (quant_vars, mempty, [])

  -- (Var χ n, Var χ' n') -> check quantification
  -- (Prd _ (AnnBind (n, a)) b, Prd _ (AnnBind (n', a')) b') -> 
  --   pure $ Just (add_bind Forall a, [(a :≗: a'), (b :≗: b')], id)

  -- TODO: this is not in Caledon!!! do we have a case prd-prd or prd-any or any-prd??? 
  (Prd (AnnBind (n, ty)) body, Prd (AnnBind (n', ty')) body') -> 
    pure $ Just (add_bind Forall n ty quant_vars, mempty, [(ty :≗: ty'), (body :≗: subst (n' ↦ Var n) body')])

  -- Case Lam-Lam
  (Abs (AnnBind (n, ty)) body, Abs (AnnBind (n', ty')) body') -> 
    pure $ Just (add_bind Forall n ty quant_vars, mempty, [(ty :≗: ty'), (body :≗: subst (n' ↦ Var n) body')])

  -- Case Lam-Any (both left and right variants)
  (s, Abs (AnnBind (n, ty)) body) -> 
    pure $ Just (add_bind Forall n ty quant_vars, mempty, [s :≗: (body `app` Var n)])
  (Abs (AnnBind (n, ty)) body, s) -> 
    pure $ Just (add_bind Forall n ty quant_vars, mempty, [(body `app` Var n) :≗: s])


  -- Note: original was matching with spine, meaning it may include more than
  -- just App (e.g. vars, ∀, ...)
  (s, s') -> do
    (atom, terms) <- case (unwind s) of
      Just v -> pure v
      _ -> throwError $ "unwinding failed for term:" <+> pretty s
    mbind <- get_elem atom quant_vars
    case mbind of
      Left bind | bind^.elem_quant == Exists -> do
        let ty = bind^.elem_type
            var = bind^.elem_name
            fors = Set.fromList $ get_foralls_after var quant_vars
            exists = Set.fromList $ get_exists_after var quant_vars
        case unwind s' of
          Just (atom', terms') -> do
            mbind' <- get_elem atom' quant_vars
            case mbind' of 
              Right ty' ->  
                if all_elements_are_vars fors terms
                then case atom' of 
                  AVar n -> gvar_const (var, terms, ty) (n, terms', ty')
                  _ -> throwError "TODO: gvar-const take an atom!"
                else pure Nothing
              Left (FBind { _elem_quant=Forall, _elem_type=ty', _elem_name=var' })
                | (not $ elem (Var var) terms) && Set.member var' fors ->
                  if not $ is_partial_perm fors terms
                  then pure Nothing
                  else throwError "gvar-uvar depends"
                | Set.member var (free_vars terms') ->
                  if not $ is_partial_perm fors terms
                  then pure Nothing
                  else throwError "occurs check failed"
                | Set.member var' fors ->
                  if is_partial_perm fors terms
                  then gvar_uvar_inside (var, terms, ty) (var', terms', ty')
                  else throwError "occurs check failed"
                | otherwise ->
                  if all_elements_are_vars fors terms
                  then gvar_uvar_outside (var, terms, ty) (var', terms', ty')
                  else throwError "occurs check failed"
              Left bind'@(FBind { _elem_quant=Exists, _elem_type=ty', _elem_name=var'}) ->
                if not $ is_partial_perm fors terms && is_partial_perm fors terms' && Set.member var' exists
                then pure Nothing
                else if var == var'
                  then gvar_gvar_same (var, terms, ty) (var', terms', ty')
                  else if Set.member var (free_vars terms')
                    then throwError "occurs check failed"
                    else gvar_gvar_diff bind (var, terms, ty) (var', terms', ty') bind'
          _ -> pure Nothing -- gvar-gvar same?? 
    
      _ -> case unwind s' of
        -- Note: HOU.hs matches with Spine, which can also include variables & constants 
        -- what to do...
        Just (atom', _) | atom /= atom' -> do
          mbind' <- get_elem atom' quant_vars
          case mbind' of 
            Left bind' | bind'^.elem_quant == Exists -> pure $ Nothing
            _ -> throwError ("can't unify two different universal equalities:" <+> pretty atom <+> "and" <+> pretty atom')
      
        -- uvar-uvar!
        Just (atom', _) | atom == atom' -> do
          throwError "not sure what a type constraint is...?"
          --let match _ _ = throwError "not sure what a type constraint is...?"
      
          --sctors <- match terms terms'
          --pure $ Just (quant_vars, mempty, [])
        _ -> throwError "can't unify a ∀-var against a term"

  where

    ------------------------------- Special Cases -------------------------------
    -- We consider now -- formulas of the form
    --     … ∃x: (u₁:A₁ → … → uₙ:Aₙ → A) … ∀y₁:B₁…yₙ:Bₙ .
    --         x yϕ(1) … yϕ(n) ≗ M
    -- for a partial permutation ϕ and branch on the structure of M 
    -- 1. GVar-Const
    -- 2. GVar-Uvar-outside
    -- 3. GVar-Uvar-inside
    -- 4. GVar-Gvar-same
    -- 5. GVar-Gvar-diff

    -- GVar-Const
    -----------------
    -- M has the form c M₁ … Mₙ for a constant c: (v₁:B₁) → … (vₙ:Bₙ) → B.
    -- here, we perform an imitation: let 
    --   L = λ [u₁:A₁ … uₙ:Aₙ] (c (x₁ u₁ … uₙ) … (xₘ u₁ … uₙ))
    -- Then, we transition to
    -- 
    -- Imitations are performed by the gvar_fixed helper function, meaning
    -- gvar_const doesn't have to do much work!
    -- TODO: change arg type to (Atom, [InternalCore], InternalCore)
    gvar_const :: (Name, [InternalCore], InternalCore) -> (Name, [InternalCore], InternalCore) -> m (UnifyResult')
    gvar_const a@(_, _, _) b@(var', _, _) =
      gvar_fixed a b $ Var . const var'

    -- GVar-Uvar Onside
    -------------------
    --
    gvar_uvar_outside :: (Name, [InternalCore], InternalCore) -> (Name, [InternalCore], InternalCore) -> m UnifyResult'
    gvar_uvar_outside = gvar_const

    -- GVar-Uvar Inside
    -------------------
    --   M has the form y
    --
    gvar_uvar_inside :: (Name, [InternalCore], InternalCore) -> (Name, [InternalCore], InternalCore) -> m UnifyResult'
    gvar_uvar_inside a@(_, terms, _) b@(var', _, _) = 
      case elem_index (Var var') $ reverse terms of
        Nothing -> pure Nothing
        Just i -> gvar_fixed a b $ Var . (!! i) 

    -- GVar-Gvar Same
    -----------------
    -- M has the form xyψ(1)…yψ(n). For some permutation ψ. Then, pick the
    -- unique permutation ρ with ρ(k) = ψ(i) for all i such that ψ(i) = ϕ(i)
    -- Perform an imitation:
    --
    -- Then, let L = λ [u₁:A₁ … uₙ:Aₙ] (x' uₚ(1) … uₚ(n)) and transition to
    --    ∃x':(u₁:Aρ(1) → ... → uₙ:Aρ(n) → A) [L/x:Tₓ]Γ,x':Tₓ F
    --
    gvar_gvar_same :: (Name, [InternalCore], InternalCore) -> (Name, [InternalCore], InternalCore) -> m UnifyResult'
    gvar_gvar_same (var, terms, ty) (_, terms', _) = do
      new_var <- fresh_var "@ggs"
      let n = length terms 
          -- abindings = bindings u₁:A₁ … uₙ:Aₙ
          abindings = take n $ fst $ telescope_type ty
          
          -- Note: we use ρ in two places: 
          --  • To create the application in the term L 
          --  • To create the type of x'
          -- Thus, instead of first calculating the permutation, then using it
          -- we intstead embed the types Aₙ and vars uₙ into the computation   
          perm = [binding | (binding,_) <- filter (\(_,(a,b)) -> a == b) $ zip abindings (zip terms terms') ]
          
          -- construct the term L
          l = untelescope (perm, lbody) where
            lbody = wind (var, (map (Var . fst . unann) perm))

          -- The type of x' : nty = u₁:Aρ(1) → ... → uₙ:Aρ(n) → A 
          nty = untelescope_type (perm, get_base n ty)
          
          sub = var ↦ l

          quant_vars' = remove_var var $
                        add_before var Exists new_var nty $
                        quant_vars

      pure $ Just (quant_vars', sub, [])
          
    -- GVar-Uvar-diff
    -----------------
    -- M has the form z yψ(1)...yψ(m) for some existentially quantified variable
    -- z : (v₁:B₁) → … → (vₘ:Bₘ) → B *distinct* from x and partial permutation ψ.
    -- 
    -- In this case, we can only transition if z is existentially quantified
    -- consecutively outside of x, i.e. x does not occur in z. (this check will
    -- already have been performed at the point we enter this function)
    -- 
    -- The transition to apply is a dual imitation: let ψ' and ϕ' be partial
    -- permitations such that if ψ(i) = ϕ(i) then there exists some k such that 
    -- ψ'(k) = i and ϕ'(k) = j
    -- Let L, L' be as follows
    -- 
    -- L = λ [u₁:A₁ ... uₙ:Aₙ] : x' uϕ(1)...uϕ(l)
    -- L' = λ [v₁:B₁ ... vₙ:Bₙ] : x' vψ(1)...vψ(l)
    -- 
    -- Then transition to
    -- Γ[  ∃x':(u₁:Aϕ'(1) → ...  uₗ:Aϕ'(1) → ??) [L'/z:Tz]Γ,x':Tₓ' [L/x:Tₓ]Γ,x':Tₓ'F ]
    --
    -------------------
    -- The above transformation is actually performed by the gvar_gvar_diff'
    -- function! The below definition (gvar_gvar_diff) will apply to any case
    -- where suitable application of the raising translation can make this rule
    -- apply. For this purpose, we have the raise_to_top function
    -- 
    -- Can be used to make it apply. 
    --
    gvar_gvar_diff :: FBind' -> (Name, [InternalCore], InternalCore) -> (Name, [InternalCore], InternalCore) -> FBind' -> m UnifyResult'
    gvar_gvar_diff top (var, terms, ty) (var', terms', _) binder =
      raise_to_top top binder (var', terms') $ \b subO -> do
        let a = (var, subst subO terms, subst subO ty)
        gvar_gvar_diff' a b

    -- See gvar_gvar_diff for more details. In short, this performs a set of 
    -- raising operations on the binding `bind'  
    raise_to_top :: FBind' -> FBind' -> (Name, [InternalCore]) -> ((Name, [InternalCore], InternalCore) -> Substitution' -> m UnifyResult') -> m UnifyResult'
    raise_to_top top binder sp m | are_adjacent top binder quant_vars =
      m (fst sp, snd sp, binder^.elem_type) mempty
    raise_to_top top binder sp m = do
      x' <- freshen (binder^.elem_name)
      let hl = reverse $ get_binds_between top binder quant_vars

          newx_args = map (Var . view elem_name) hl 

          sub = (binder^.elem_name) ↦ wind (x', newx_args)

          ty' = untelescope_type (map (\fb -> AnnBind (fb^.elem_name, fb^.elem_type)) hl, binder^.elem_type)

          add_sub result = case result of 
            Nothing -> pure Nothing
            -- TODO: consult hou - seems to perform substitution twice?? 
            Just (quant_vars, sub', cons) ->  
              let sub'' = (subst sub' <$> sub) <> sub' 
                  quant_vars' = subst sub' quant_vars
              in pure $ Just (quant_vars', sub'', cons)

          update_binds bs = subst sub
                      $ add_after (top^.elem_name) Exists x' ty'
                      $ remove_bind top bs 

      result <- add_sub =<< m (fst sp, subst sub (snd sp), ty') sub
      pure $ fmap (\(quant_vars, sub, cons) -> (remove_var x' $ update_binds quant_vars, sub, cons)) result

    -- See gvar_gvar_diff for more details
    gvar_gvar_diff' :: (Name, [InternalCore], InternalCore) -> (Name, [InternalCore], InternalCore)-> m UnifyResult'
    gvar_gvar_diff' (var, terms, ty) (var', terms', ty') = do
      -- ty <- regen ty 
      -- ty' <- regen ty'
      new_var <- fresh_var "@ggd"
      let n = length terms
          m = length terms'

          abindings = take n $ fst $ telescope_type ty
          bbindings = take m $ fst $ telescope_type ty'

          perm = do
            (iyt,y) <- zip abindings terms
            (i',_) <- filter (\(_,y') -> y == y') $ zip (fmap aname bbindings) terms' 
            pure (iyt,i')

          l = untelescope (abindings, wind (new_var, fmap (Var . aname . fst) perm))
          l' = untelescope (bbindings, wind (new_var, fmap (Var . snd) perm))

          newty = untelescope_type (map fst perm, get_base n ty) 

          sub = (var' ↦ l') <> (var ↦ l)

          quant_vars' = remove_var var $
                        remove_var var' $
                        add_before var Exists new_var newty $ quant_vars


        in pure $ Just (quant_vars', sub, [] {- var xN :@: xNty] -} )

    -- GVar-Fixed
    -----------------
    -- While not a specific rule in itself, Gvar-fixed is useful as helper when
    -- M has the form c M₁ … Mₙ for a fixed c, (constant/universally quantified)
    -- c : (v₁:B₁) → … (vₘ:Bₘ) → B.
    -- here, we perform an imitation: let 
    --   L = λ [u₁:A₁ … uₙ:Aₙ] (c (x₁ u₁ … uₙ) … (xₘ u₁ … uₙ))
    -- Then, we transition to
    --   ∃x₁: (u₁:A₁) → (uₙ:Aₙ) → B₁ ...
    --     ∃xₘ: (u₁:A₁) → (uₙ:Aₙ) → [(xₘ₋₁ u₁ … uₙ/v₁) … (x₁ u₁ … uₙ/vₘ)] Bₘ ...
    --       [L/x]F
    -- 
    gvar_fixed :: (Name, [InternalCore], InternalCore) -> (Name, [InternalCore], InternalCore) -> ([Name] -> InternalCore) -> m UnifyResult'
    gvar_fixed (var, terms, ty) (var', terms', ty') action = do
      let get_tybinds = fst . telescope_type

          aₙₛ = get_tybinds ty  -- The bindings u₁:A₁ … uₙ:Aₙ 
          bₘₛ = get_tybinds ty' -- The bindings v₁B₁ … vₙ:Bₙ

      -- TOOD: confirm below is true: consider use in toLTerm?
      -- the vector of bindings x₁: (∪_1:A₁) → … (uₙ:Aₙ) → B, …,
      --   xₘ (∪_1:A₁) → … (uₙ:Aₙ) → [(xₘ₋₁ u₁ … uₙ/v₁) … (x₁ u₁ … uₙ/vₘ)]B
      xₘₛ <- forM bₘₛ $ \_ -> do
        x <- fresh_var "@xm"
        pure $ (x, wind (x, map (Var . aname) aₙₛ))

      let to_l_term term = case term of
              Prd bind body -> Abs bind $ to_l_term body
              _ -> foldr app (action $ fmap aname aₙₛ) $ map snd xₘₛ
          -- The term L, which we will substitute for x
          l = to_l_term ty

          vbuild e = untelescope_type (aₙₛ, e)

          -- produce the set of substitutions starting at [] and ending with
          -- [(xₘ₋₁ u₁ … uₙ/v₁) … (x₁ u₁ -- … uₙ/vₘ)] m, which can then be
          -- applied to B (see transition in description)
          subst_bty :: Substitution' -> InternalCore -> [(Name, InternalCore)] -> m [(Name, InternalCore)]
          subst_bty sub term l = case (term,l) of 
            (Prd b ty, (x, xi):xmr) ->
              (:) (x, vbuild $ subst sub (snd $ unann b))
                <$> (subst_bty (insert (aname b) xi sub) ty xmr)
            (_, []) -> pure []
            _ -> throwError "_ is not well typed for _ on _"

          sub = var ↦ l

      quant_vars' <- subst sub
        <$> remove_var var
        <$> foldr ($) quant_vars
        <$> fmap (\(n, ty) -> add_after var Exists n ty)
        <$> (subst_bty mempty ty' xₘₛ)

      -- TODO: quant_vars'
      pure $ Just ( quant_vars'
                  , sub
                  -- application of sub to wind (var, terms) seems to be related
                  -- to a bug in HOU.hs (Caledon)
                  , [subst sub (wind (var, terms)) :≗: wind (var', terms')])


    -------------------------------- Predicates ---------------------------------
    -- These functions correspond to particular properties of an object(s)

    -- Returns true if the second argument is a partial permutation of the first
    is_partial_perm :: Set Name -> [InternalCore] -> Bool
    is_partial_perm fors = go mempty where
      go _ [] = True
      go s (Var n : rest) =
         Set.member n fors && not (Set.member n s) && go s rest
      go _ _ = False

    -- Returns true if the second argument consists solely of variables found in
    -- the first
    all_elements_are_vars :: Set Name -> [InternalCore] -> Bool
    all_elements_are_vars fors = go where
      go [] = True
      go (Var n : vars) = Set.member n fors && go vars
      go _ = False


{--------------------------- UNIFYING FOR HABITATION ---------------------------}
{- Unifying for habitation is similar to unification for equality, in that     -}
{- we apply transformations based on the structure of terms                    -}
{-                                                                             -}
{- However, the search may generate a new type of constraint not present in    -}
{- 'regular' formulas. These are constraints of the form A ∈ B >> A' ∈ B'.     -}
{- These constraints are satisfied if the truth of the LHS (A ∈ B) implies     -}
{- the RHS (A' ∈ B'). The two constraint types (A ∈ B) and (A ∈ B >> A' ∈ B')  -}
{- can be solved through mutal recursion on two functions: left-search and     -}
{- right-search.                                                               -}
{-------------------------------------------------------------------------------}


-- TODO: development of the search algorithm is temporarily halted
-- this is because we do not have any notion of /constants/ which can be
-- assigned types / type families
  
{-
right_search :: InternalCore -> InternalCore -> ContT a UnifyM (Mabye [SingleConstraint' χ])
right_search env m goal cont = 
  case goal of 

    -- Rule G Π: M ∈ (x:A) → B ⇒ ∀x: A.∃y: B.(y ≗ M x) ∧ y ∈ B

    Prd _ _ a b -> 
      let m' = shift 2 0 m
          b' = shift 1 0 b
          b'' = shift 2 0 b

          x = var 1 "x"
          y = var 0 "y"
      in cont $ Just (\env -> (bind Forall "x" a) (bind Exists "y" a),
                      [y :≗: m' `app` x, y :∈: b'']) 

    _ -> case unwind goal of
      -- G Atom 1 / G Atom 2
      -- ∀x:A. F[M ∈ C] ⇒ ∀x:A. F[x ∈ A >> M ∈ C]
      --         M ∈ C  ⇒ c₀ ∈ C >> M ∈ C 
      -- for c₀ a constant

      
      Just (var, terms) -> 

        -- if there are no existentials in m or the goal, then we cannot do anything 
        if all is_fixed (free_vars m <> free_vars goal) then
          cont $ Just []

        -- otherwise
        else case targets of 
          [] -> cont $ Nothing

          

        
      Nothing -> throwError ("can't: right-search with goal :" <> pretty goal)

    

left_search (m, goal) (x, target) = left_cont x target
  where
    left_cont n target = case target of
      -- Rule D Π:
      --   F[N ∈ (x:A) → B >> M ∈ C] → F[∃x:A . (N x ∈ B >> M ∈ C) ∧ x ∈ A]

      Prd _ _ a b -> 
        let x' = var 0 "x"
            a' = shift 1 0 a
         in left_cont (shift 1 0 (n `app` x')) (shift 1 0 (b `app` x')) <> [x' :∈: a']
      Abs _ _ _ _ -> throwError ("λ does not have type atom" <> pretty target)

      -- Rule D Atom:
      --   ????
      _ -> pure $ [goal :≗: target, m :≗: n]
-}

{------------------------------ BINDING FUNCTIONS ------------------------------}
{- These are functions to adjust bindings in flat formulas.                    -}
{- add : Add a binding at the lowest level                                     -}
{-------------------------------------------------------------------------------}

(!) :: (MonadError (Doc ann) m) => Name -> Binds a -> m (FBind a)
name ! (b:bs) 
  | b^.elem_name == name = pure $ b
  | otherwise = name ! bs
name ! [] = throwError $ "couldn't find binding: " <+> pretty name

get_exists_after :: Name -> (Binds a) -> [Name]
get_exists_after name binds =
  map (view elem_name) $ 
    drop_until ((== name) . view elem_name) $ 
      filter ((== Exists) . view elem_quant)
      binds

get_foralls_after :: Name -> (Binds a) -> [Name]
get_foralls_after name binds =
  map (view elem_name) $ 
    drop_until ((== name) . view elem_name) $ 
      filter ((== Forall) . view elem_quant)
      binds

get_binds_between :: (FBind a) -> (FBind a) -> (Binds a) -> (Binds a)
get_binds_between top bottom binds =
  between (== top) (== bottom) binds
  where
    between f g (x:xs)
      | f x = drop_until g xs
      | otherwise = between f g xs
    between _ _ [] = []

split_until :: (a -> Bool) -> [a] -> ([a], [a])
split_until f (x:xs)
  | f x = (_1 %~ (:) x) $ split_until f xs
  | otherwise = (_2 %~ (:) x) $ split_until f xs
split_until _ [] = ([], [])

drop_until :: (a -> Bool) -> [a] -> [a]
drop_until p = fst . split_until p

-- take_until :: (a -> Bool) -> [a] -> [a]
-- take_until p = snd . split_until p

split_before :: (a -> Bool) -> [a] -> ([a], [a])
split_before p = go
  where go [] = ([], [])
        go (x:xs) 
         | p x = ([], x:xs) 
         | otherwise = (_1 %~ (:) x) $ go xs
  
split_after :: (a -> Bool) -> [a] -> ([a], [a])
split_after p = go
  where go [] = ([], [])
        go (x:xs) 
         | p x = ([x], xs) 
         | otherwise = (_1 %~ (:) x) $ go xs

remove_var :: Name -> Binds a -> Binds a
remove_var var = filter $ (/= var) . view elem_name

remove_bind :: FBind a -> Binds a -> Binds a
remove_bind bind = filter (/= bind)

add_bind :: Quant -> Name -> a -> Binds a -> Binds a
add_bind quant name ty = (:) (FBind quant name ty)

are_adjacent :: FBind a -> FBind a -> (Binds a) -> Bool
are_adjacent a b vars =  
  any_of (== (a, b)) (zip vars (tail vars))
  where
    any_of pred = List.foldl' (||) False . map pred

add_before :: Name -> Quant -> Name -> a -> Binds a -> Binds a
add_before n quant name val bindings =
  let (beg, end) = split_before ((== n) . view elem_name) bindings 
  in beg <> [(FBind quant name val)] <> end

add_after :: Name -> Quant -> Name -> a -> Binds a -> Binds a
add_after n quant name val bindings =
  let (beg, end) = split_after ((== n) . view elem_name) bindings 
  in beg <> [(FBind quant name val)] <> end

elem_index :: Eq a => a -> [a] -> Maybe Int
elem_index = List.elemIndex  
    

{-------------------------------- TRANSFORMERS ---------------------------------}
{- These functions are internal utility functions for manipulating Sigil. terms -}
{-                                                                             -}
{- wind and unwind are for converting between the forms:                       -}
{-                     (x A B C D) ⟺ (x, [A, B, C, D])                         -}
{- Where x is a variable, and A B C are normal                                 -}
{-                                                                             -}
{- telescope and untelescope are for converting between the forms              -}
{-             λx:A↦λy:B↦...↦ body ⟺ ([x, y, ...], body)                       -}
{-                                                                             -}
{- telescope_type and untelescope_type are for converting between the forms:   -}
{-        (x:A₁)→...→(z:Aₙ) → body ⟺ ([x, ..., z], body)                       -}
{-                                                                             -}
{- flatten: hoist all bindings as far out as possible, e.g. convert            -}
{-     (∃x:T₁. M ≗ N) ∧ (∀yT₂. A ∈ B) into (∃x:T₁. ∀y:T₂. (M ≗ N ∧ A ∈ B)      -}
{- care has to be taken to avoid capturing variables.                          -}
{-------------------------------------------------------------------------------}


get_elem :: (MonadError (Doc ann) m) => Atom -> Binds' -> m (Either FBind' InternalCore)
get_elem atom qvars = case atom of
  AVar n -> Left <$> n ! qvars 
  AUni n -> pure $ Right (Uni n) 

unwind :: InternalCore -> Maybe (Atom, [InternalCore])        
unwind core = case core of 
  App l r -> (_2 %~ (r :)) <$> (unwind l)
  Var n -> Just (AVar n, [])
  Uni n -> Just (AUni n, [])
  _ -> Nothing

wind :: (Name, [InternalCore]) -> InternalCore
wind (n, vars) = foldr App (Var n) vars  
    
-- telescope :: Core b n χ -> ([b n (Core b n χ)], Core b n χ)
-- telescope term = case term of
--   Abs χ b body -> (_1 %~ (:) b) $ telescope body
--   a -> ([], a)

untelescope :: ([AnnBind Name InternalCore], InternalCore) -> InternalCore
untelescope (bindings, body) = foldr Abs body bindings

telescope_type :: InternalCore -> ([AnnBind Name InternalCore], InternalCore)
telescope_type term = case term of
  Prd binding b -> (_1 %~ (:) binding) $ telescope_type b
  a -> ([], a)

untelescope_type :: ([AnnBind Name InternalCore], InternalCore) -> InternalCore
untelescope_type (bindings, ty) = foldr Prd ty bindings
  
flatten :: Formula a -> FlatFormula a
flatten formula = case formula of
  Conj cs -> FlatFormula [] cs
  And l r -> flatten l <> flatten r
  Bind q n ty f -> (binds %~ (:) (FBind q n ty)) $ flatten f 

get_base :: Int -> InternalCore -> InternalCore 
get_base 0 a = a                            
get_base n (Abs _ r) = get_base (n - 1) r
get_base _ a = a



{------------------------------- MISC. INSTANCES -------------------------------}



-- Helper functions that maybe can be moved to another file??  

app :: InternalCore -> InternalCore -> InternalCore  
app val arg = case val of 
  Abs (AnnBind (n, _)) e -> subst ((n ↦ arg) :: Substitution') e
  _ -> App val arg 

aname :: AnnBind n b -> n
aname (AnnBind (n, _)) = n
