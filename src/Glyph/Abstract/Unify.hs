{-# LANGUAGE ScopedTypeVariables #-}
module Glyph.Abstract.Unify
  (Formula(..),
   SingleConstraint(..),
   Quant(..),
   Unifiable(..)) where

{--------------------------------- UNIFICATION ---------------------------------}
{- This file contains a Higher Order Unification Algorithm for the Glyph       -}
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
{- • ∃n:ℕ∃. T:𝒰 n. M ∈ T is equivalent to inferring the type of M              -}
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


import Control.Monad.Except (MonadError)
import Control.Monad.Reader (MonadReader)
-- import Control.Monad.Except (MonadError, throwError, 
--                              Except, runExcept)
-- import Control.Monad.Reader (MonadReader, ask,
--                              ReaderT, runReaderT)
-- import Control.Monad.Identity (Identity)
-- import Control.Applicative
-- import Control.Lens (makeLenses, (^.), (%~))
--import Data.Monoid
-- import qualified Data.Set as Set
-- import Data.Set (Set)
-- import qualified Data.Map as Map
-- import Data.Map (Map, (!)) 
--import qualified Data.List as List
import Data.Text (Text)  

import Prettyprinter

-- import Glyph.Abstract.Syntax
--import Glyph.Abstract.Term
import Glyph.Abstract.Environment
import Glyph.Abstract.Substitution

  
{------------------------------ TYPE DEFINITIONS -------------------------------}
{- The types here are for the most part direct translations of types mentioned -}
{- above, and form the public interface to this module.                        -}
{-                                                                             -}
{- Note the slight modification to the Formula Type - it is now split in two:  -}
{- SingleConstraint, and Formula. This is because many helper functions.       -}
{- Focus on solving one (or more) single constraints, and so having a separate -}
{- type for them makes giving types to these functions easier.                 -}
{-                                                                             -}
{- The Unifiable typeclass represents terms which can be unified when placed   -}
{- in a formula, and is based on the solve. Method.                            -}
{-------------------------------------------------------------------------------}


class Unifiable a where
  solve :: (Environment Name e, MonadError (Doc ann) m, MonadGen m, MonadReader (e a) m) => Formula a -> m (Substitution a)
  --solve_isolated :: Env a -> Formula a -> Either (Doc ann) (Substitution a)

data SingleConstraint a
  = a :≗: a -- Claim of Unifiability of two terms
  | a :∈: a -- Claim of type occupation 

data Quant = Exists | Forall

data Formula a
  = Conj [SingleConstraint a]     -- Conjuntion of n single constraints ([] = ⊤)
  | And (Formula a) (Formula a)   -- Conjunction of two formulas
  | Bind Quant Text a (Formula a) -- Quantified (∀/∃) formulas


instance Functor SingleConstraint where  
  fmap f con = case con of 
    a :≗: b -> f a :≗: f b
    a :∈: b -> f a :∈: f b

instance Subst Name s a => Subst Name s (SingleConstraint a) where  
  subst sub con = case con of 
    a :≗: b -> subst sub a :≗: subst sub b
    a :∈: b -> subst sub a :∈: subst sub b

instance (Subst Name s a) => Subst Name s (Formula a) where
  subst sub term = case term of 
    Conj l -> Conj $ map (subst sub) l
    And l r -> And (subst sub l) (subst sub r)
    Bind quant var ty body -> Bind quant var (subst sub ty) (subst sub body)
  


{----------------------------- INTERNAL DATATYPES ------------------------------}
{- TODO: Unification Monad, env and Binds                                      -}
{-                                                                             -}
{- These types re are for the most part direct translations of types mentioned -}
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
{- procedure is encapsulated in the 'UnifyResult' type. 'UnifyResult'          -}
{- contains two members:                                                       -}
{- • A function which will add or remove Bindings                              -}
{- • A substitution to apply.                                                  -}
{-------------------------------------------------------------------------------}

{--
-- type Unify ann v = ReaderT (Env v) (Except (Doc ann))

-- Bindings: a value is either bound within a formula (and hence quantified)
type Env = []
type Binds a = Map.Map Integer (Quant, a)

type ContT a m c = ((c -> m a) -> m a)

type UnifyResult a =
  Maybe ( Binds a
        , Substitution a
        , [SingleConstraint a])

class UnifyResultM 

unifyempty = (id, [], id)

data FlatFormula a = FlatFormula
  { _binds :: Binds a
  , _constraints :: [SingleConstraint a]
  }

data Binding a = Binding
  { _elem_name :: IDName
  , _elem_quant :: Quant
  , _elem_type :: a
  }

type Env' χ              = Env (Core IDName χ)
type Core' χ             = Core IDName χ
type Binds' χ            = [(Quant, Core IDName χ)]
type Binding' χ          = Binding (Core IDName χ)
type Formula' χ          = Formula (Core IDName χ)
type UnifyResult' χ      = UnifyResult (Core IDName χ)
type FlatFormula' χ      = Formula (Core IDName χ)
type Substitution' χ     = Substitution (Core IDName χ)
type SingleConstraint' χ = SingleConstraint (Core IDName χ)

makeLenses ''FlatFormula
makeLenses ''Binding
  

{---------------------------- TOP-LEVEL UNIFICATION ----------------------------}
{- The solve function is the top-level procedure, and the driver is the        -}
{- uni_while function. This will perform successive transformations until a    -}
{- formula is in 'solved form'                                                 -}
{-------------------------------------------------------------------------------}


instance forall χ. Term (Core IDName χ) => Unifiable (Core IDName χ) where
  solve = fst <$> uncurry (flip uni_while mempty) . (\v -> (v^.binds, v^.constraints)) . flatten where

    uni_while :: forall m ann. (MonadError (Doc ann) m, MonadGen m, MonadReader (Env' χ) m) =>
                 Binds' χ -> Substitution' χ -> [SingleConstraint' χ] -> m (Substitution' χ, [SingleConstraint' χ])
    uni_while quant_vars sub cs = 
      let --uni_with :: (MonadError (Doc ann) m, MonadReader (Env' χ) m) => (SingleConstraint' χ -> ContT b m (UnifyResult' χ))
          --  -> (Substitution' χ, [SingleConstraint' χ]) -> m (Substitution' χ, [SingleConstraint' χ])
          uni_with f backup = search_in cs []
            where
              search_in :: (MonadError (Doc ann) m, MonadGen m, MonadReader (Env' χ) m) =>
                [SingleConstraint' χ] -> [SingleConstraint' χ] -> m (Substitution' χ, [SingleConstraint' χ])
              search_in [] _ = finish Nothing
              search_in (next:rest) resolved = 
                f quant_vars next $ \case
                -- TODO: take into account update to UnifyResult
                  Just (new_fctx, sub', next) ->
                    let
                      formula  = FlatFormula new_fctx (reverse resolved <> [next] <> rest)
                      formula' = subst sub' formula
                    in finish $ Just (sub', formula'^.constraints, formula'^.binds)
                  Nothing -> search_in rest (next:resolved)

              finish :: (MonadError (Doc ann) m, MonadGen m, MonadReader (Env' χ) m) =>
                Maybe (Substitution' χ, [SingleConstraint' χ], Binds' χ) -> m (Substitution' χ, [SingleConstraint' χ])
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

    unify_one :: (MonadError (Doc ann) m, MonadGen m, MonadReader (Env' χ) m) =>
      Binds' χ -> SingleConstraint' χ -> ContT r m (UnifyResult' χ)
    unify_one binds constraint cont = case constraint of 
      a :≗: b -> do
        c' <- unify_eq binds a b
        case c' of 
          Nothing -> cont =<< unify_eq binds b a
          r -> cont r
      _ -> cont Nothing
    
    unify_search :: (MonadError (Doc ann) m, MonadGen m, MonadReader (Env' χ) m) =>
      Binds' χ -> SingleConstraint' χ -> ContT r m (UnifyResult' χ)
    unify_search binds constraint cont = case constraint of
      --a :∈: b | not_higher_universe b -> right_search binds a b $ new_cont cont
      _ -> cont Nothing
      where 
        not_higher_universe (Uni _ k) = k < 1
        not_higher_universe _ = True
    
    unify_search_atom :: (MonadError (Doc ann) m, MonadGen m, MonadReader (Env' χ) m) =>
      Binds' χ ->  SingleConstraint' χ -> ContT r m (UnifyResult' χ)
    unify_search_atom binds constraint cont = case constraint of
      --a :∈: b -> right_search binds a b $ new_cont cont
      _ -> cont Nothing
    
    new_cont cont constraint = cont $ fmap (\v -> (mempty, v, False)) constraint
      

  -- solve_isolated env formula = runExcept $ runReaderT env $
  --   (solve formula :: ReaderT (Env' χ) (Except (Doc ann)) (Substitution (Core Name χ)))


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


unify_eq :: (MonadError (Doc ann) m, MonadGen m, MonadReader (Env' χ) m) =>
  (Binds' χ) -> Core IDName χ -> Core IDName χ -> m (UnifyResult' χ)
unify_eq quant_vars a b = case (a, b) of 
  (Coreχ χ, Coreχ χ') ->
    if χ == χ'
    then Just (id, mempty, id)
    else throwError "unequal Coreχ values"
  (Uni _ n, Uni _ n') ->
    if n == n'
    then Just (id, mempty, id)
    else throwError ("unequal universes: (𝒰 " <> n <> ") and (𝒰 " <> n' <> ")")

  -- Terms which are otherwise equal
  (s, s') | s == s' -> Just (id, mempty, id)

  -- (Var χ n, Var χ' n') -> check quantification
  (Prd _ _ a b, Prd _ _ a' b') -> 
    pure $ Just (add_bind Forall a, [(a :≗: a'), (b :≗: b')], id)

  -- Case Lam-Lam
  (Abs _ _ ty body, Abs _ _ ty' body') -> 
    pure $ Just (add_bind Forall ty, [(ty :≗: ty'), (body :≗: body')], id)

  -- Case Lam-Any (both left and right variants)
  (s, Abs _ v ty body) -> 
    pure $ Just (add_bind Forall ty, [s :≗: (body `app` mkvar 0 v)], id)
  (Abs _ v ty body, s) -> 
    pure $ Just (add_bind Forall ty, [(body `app` mkvar 0 v) :≗: s], id)

  -- Note: original was matching with spine, meaning it may include more than
  -- just App (e.g. vars, ∀, ...)
  (s, s') -> do
    (var, terms) <- case (unwind s) of
      Just v -> pure v
      _ -> (throwError "ran out of unify terms")
    bind <- var ! quant_vars
    if bind^.elem_quant == Exists then do
      let ty = bind^.elem_type
      fors <- get_foralls_after var binds
      exists <- get_exists_after var binds
      case unwind s' of
        Just (var', terms') -> do
          bind' <- var' ! quant_vars
          case bind' of 
            Binding { _elem_quant=Forall, _elem_type=ty' }
              | (not $ elem (mkvar var) terms) && Set.member var' fors ->
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
            Binding { _elem_quant=Exists, _elem_type=ty'} ->
              if not $ is_partial_perm fors terms && is_partial_perm fors terms' && Set.member var' exists
              then pure Nothing
              else if var == var'
                then gvar_gvar_same (var, terms, ty) (var', terms', ty')
                else if Set.member var (free_vars terms')
                  then throwError "occurs check failed"
                  else gvar_gvar_diff bind (var, terms, ty) (var', terms', ty') bind'
        _ -> pure Nothing -- gvar-gvar same?? 
    
    else case unwind s' of
      -- Note: HOU.hs matches with Spine, which can also include variables & constants 
      -- what to do...
      Just (var', _) | var /= var' -> do
        bind' <- var' ! quant_vars
        if bind'^.elem_quant == Exists
          then pure $ Nothing
          else throwError "can't unify two different universal equalitiies"
    
      -- uvar-uvar!
      Just (var', terms') | var == var' -> do
        let match = throwError "not sure what a type constraint is...?"
    
        sctors <- match terms terms'
        pure $ Just (id, mempty, id)
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
    gvar_const a@(_, _, _) b@(var', _, _) =
      gvar_fixed a b $ flip mkvar "s"  . const var'

    -- GVar-Uvar Onside
    -------------------
    --
    gvar_uvar_outside (var, terms, ty) (var', terms', ty') = gvar_const

    -- GVar-Uvar Inside
    -------------------
    --   M has the form y
    --
    gvar_uvar_inside a@(_, terms, _) b@(var', _, _) = 
      case elem_index var' $ reverse terms of 
        Nothing -> pure Nothing
        Just i -> gvar_fixed a b $ (!! i)

    -- GVar-Gvar Same
    -----------------
    -- M has the form xyψ(1)…yψ(n). For some permutation ψ. Then, pick the
    -- unique permutation ρ with ρ(k) = ψ(i) for all i such that ψ(i) = ϕ(i)
    -- Perform an imitation:
    --
    -- Then, let L = λ [u₁:A₁ … uₙ:Aₙ] (x' uₚ(1) … uₚ(n)) and transition to
    --    ∃x':(u₁:Aρ(1) → ... → uₙ:Aρ(n) → A) [L/x:Tₓ]Γ,x':Tₓ F
    --
    gvar_gvar_same (var, terms, ty) (_, terms', _) = do
      var <- fresh_var 
      let n = length terms 
          -- atys = types Aₙ
          -- a    = the type A
          (atys, a) = (\(as, a) -> (take n as, a)) $ telescope_type ty
          
          -- Note: we use ρ in two places: 
          --  • To create the application in the term L 
          --  • To create the type of x'
          -- Thus, instead of first calculating the permutation, then using it
          -- we intstead embed the types Aₙ and vars uₙ into the computation   
          -- TODO: adapt to DeBruijn terms
          perm = [t | t <- filter (\(x,y) -> x == y) (zip terms terms')]
          
          -- construct the term L
          l = untelescope ((map fst perm), lbody) where
            lbody = wind (var, (map snd perm))
          
          -- The substitution to perform (TODO 
          -- TODO: adapt to DeBruijn terms
          sub = var ↦ l

          -- The type of x' : nty = u₁:Aρ(1) → ... → uₙ:Aρ(n) → A 
          nty = foldr (Abs undefined "s") a (map fst perm)

          modify_binds = remove_bind var . add_before var Exists nty

      pure $ Just ((modify_binds . subst sub), [], id)
          
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
    gvar_gvar_diff top (var, terms, ty) (var', terms', ty') bind =
      raise_to_top top bind (var', terms') $ \b subO -> do
        let a = (subst subO var, subst subO terms, subst subO ty)
        gvar_gvar_diff' a b

    -- See gvar_gvar_diff for more details. In short, this performs a set of 
    -- raising operations on the binding `bind'  
    raise_to_top top bind sp m | are_adjacent quant_vars top bind =
      m (sp, ty) mempty
    raise_to_top top bind sp m = do
      x' <- freshen (bind^.elem_name)
      let mod1 = (remove_bind top. add_after top x' Exists ty')
          
          hl = reverse $ get_binds_between top bind quant_vars
          newx_args = x 

          sub = x ↦ (wind x' newx_args)

          add_sub result = case result of 
            Nothing -> pure Nothing
            -- TODO: consult hou - seems to perform substitution twice?? 
            Just (mod1, sub, cons) ->  
              
              pure $ Just (subst sub' . mod1, sub ⋅ sub', cons)

      pure (mod, sub, remove_bind x)

    -- See gvar_gvar_diff for more details
    gvar_gvar_diff' (var, terms, ty) (var', terms', ty') = do
      let n = length terms
          m = length terms'

          (uNL, atyl) = unzip $ take n $ fst $ untelescope_type ty
          (vNl, btyl) = unzip $ take m $ fst $ untelescope_type ty'

          perm = do
            (iyt,y) <- zip (zip uNl atyl) yl
            (i',_) <- filter (\(_,y') -> y == y') $ zip vNl y'l 
            pure (iyt,i')

          l = untelescope ((fst perm), mkvar new_var) (unwind (snd perm))
          l' = untelescope ((fst perm), mkvar new_var) (unwind (snd perm))

          xnewty = foldr (uncurry forall) (getBase n aty) (map fst perm)

          sub = (var' ↦ l') *** (var ↦ l)

          binds' = remove_env sub $ add_before var Exists xnew xnewty $ quant_vars

        in pure $ Just (sub, [] {- var xN :@: xNty] -}, False, binds')

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
    gvar_fixed a@(var, _, ty) b@(var', _, ty') action = do
      let get_tyargs = fst . telescope_type

          aₙₛ = get_tyargs ty  -- The types A₁ … Aₙ 
          bₙₛ = get_tyargs ty' -- The types B₁ … Bₙ

          -- The term L, which we will substitute for x
          l = getDepth var

      pure $ Just (id, subst sub $ a :≗: b, id)


    -------------------------------- Predicates ---------------------------------
    -- These functions correspond to particular properties of an object(s)

    -- Returns true if the second argument is a partial permutation of the first
    is_partial_perm :: Set Int -> [Core IDName χ] -> Bool
    is_partial_perm fors = go mempty where
      go _ [] = True
      go s (Var _ (UniqueName n _) : rest) =
         Set.member n fors && not (Set.member n s) && go s rest
      go _ _ = False

    -- Returns true if the second argument consists solely of variables found in
    -- the first
    all_elements_are_vars :: Set Int -> [Core IDName χ] -> Bool
    all_elements_are_vars fors = go where
      go [] = True
      go (Var _ (UniqueName n _) : vars) = Set.member n fors
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
right_search :: Core' χ -> Core' χ -> ContT a UnifyM (Mabye [SingleConstraint' χ])
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


get_exists_after :: Int -> (Binds a) -> [a]
get_exists_after n binds =
  map snd $ filter (\(q, _) -> q == Exists) $ drop (n - length binds) binds

get_foralls_after :: Int -> (Binds a) -> [a]
get_foralls_after n binds =
  map snd $ filter (\(q, _) -> q == Forall) $ drop (n - length binds) binds

remove_bind :: Int -> FlatFormula a -> FlatFormula a
remove_bind val = (binds %~ (:) (quant, val)) . (constraints %~ shift 1 0)

add_bind :: Quant -> a -> FlatFormula a -> FlatFormula a
add_bind quant val =
  (binds %~ (:) (quant, val)) . (constraints %~ shift 1 0)

add_before :: Int -> Quant -> a -> FlatFormula a -> FlatFormula a
add_before n quant val formula =
  let beg = take n (formula^.binds) 
      end = drop n (formula^.binds) 
  in FlatFormula
    (beg <> [(quant, val)] <> shift 1 0 end)
    (shift 1 0 (formula^.constraints))

add_after :: Int -> Quant -> a -> FlatFormula a -> FlatFormula a
add_after n quant val formula =
  let beg = take n (formula^.binds) 
      end = drop n (formula^.binds) 
  in FlatFormula
    (beg <> [(quant, val)] <> shift 1 0 end)
    (shift 1 0 (formula^.constraints))

mkvar :: Int -> Text -> Core IDName χ  
mkvar n s = Var undefined (Debruijn n s)

elem_index :: Eq a => a -> [a] -> Maybe Int
elem_index = List.elemIndex  
    

{-------------------------------- TRANSFORMERS ---------------------------------}
{- These functions are internal utility functions for manipulating glyph terms -}
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


unwind :: Core' χ -> Maybe (Int, [Core' χ])        
unwind core = case core of 
  App _ l r -> (_1 %~ (r :)) <$> (unwind l) 
  Var _ (UniqueName n _) -> Just (n, [])
  Var _ (QIDName _) -> Nothing
  _ -> Nothing

wind :: (Int, [Core' χ]) -> Core' χ
wind (n, vars) = foldr (App undefined) (Var $ DeBruijn n "s") vars  
    
telescope :: MonadError (Doc ann) m => Core n χ -> m ( [Core n χ], Core n χ)
telescope term = case term of
  Abs χ var body -> (\(end, as) -> (end, a:as)) <$> telescope b
  a -> (a, [])

untelescope :: ([Core' χ], Core' χ) -> Core' χ
untelescope (list, seed) = foldr (Prd undefined "s") list seed

telescope_type :: Core n χ -> ([Core n χ], Core n χ)
telescope_type term = case term of
  Prd χ var a b -> (\(end, as) -> (end, a:as)) <$> telescope_type b
  a -> (a, [])

untelescope_type :: ([Core n χ], Core n χ) -> Core n χ
untelescope_type (list, seed) = foldr (Prd undefined "s") list seed
  
flatten :: Formula a -> FlatFormula a
flatten formula = case formula of
  Conj cs -> FlatFormula [] cs
  And l r -> flatten l <> flatten r
  Bind q _ ty f -> (binds %~ Map.insert q ty) . flatten f 


{------------------------------ PRETTY INSTANCES -------------------------------}


instance Pretty Quant where 
  pretty Exists = "∃"
  pretty Forall = "∀"

instance Pretty a => Pretty (SingleConstraint a) where  
  pretty s = case s of 
    a :≗: b -> "(" <> pretty a <+> "≗" <+> pretty b <> ")"
    a :∈: ty -> "(" <> pretty a <+> "∈" <+> pretty ty <> ")"

instance Pretty a => Pretty (Formula a) where
  pretty f = case f of 
    Conj fs -> case fs of 
      [] -> "⊤"
      _ -> (foldl (<+>) "" . List.intersperse "∧" . map pretty) fs
    And l r ->
      "(" <> pretty l <+> "∧" <+> pretty r <> ")"
    Bind quant nm ty f' ->
      pretty quant <> pretty nm <> ":" <+> pretty ty <> "." <+> pretty f'


{------------------------------- MISC. INSTANCES -------------------------------}


instance Monoid (FlatFormula a) where
  mempty = FlatFormula [] []

  mappend f1 f2 = FlatFormula bs scons where
    bs = f1^.binds <> shift (nvars f1) 0 (f2^.binds)
    scons = f1^.constraints <> shift (nvars f1) 0 (f2^.constraints)

    nvars = length . _binds 

--}
