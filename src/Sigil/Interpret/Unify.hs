{-# LANGUAGE ScopedTypeVariables, InstanceSigs, ImplicitParams #-}
--{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Interpret.Unify
  -- Exports: Unify instnace for InternalCore
  ( solve ) where


{--------------------------------- UNIFICATION ---------------------------------}
{- This file contains a Higher Order Unification Algorithm for the Sigil.      -}
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
import Control.Applicative (Alternative)
import Control.Lens (_1, _2, makeLenses, (^.), (%~), view, bimap, over, mapped)
import Data.Text (Text)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.List as List
import Data.Foldable (asum)

import Prettyprinter
import Prettyprinter.Render.Sigil (SigilDoc)

import Sigil.Abstract.Unify
import Sigil.Abstract.AlphaEq
import Sigil.Abstract.Names
import qualified Sigil.Abstract.Substitution as Sub
import Sigil.Abstract.Substitution hiding (empty, lookup, insert)

import Sigil.Concrete.Internal
import Sigil.Concrete.Decorations.Implicit
import Sigil.Interpret.Canonical.Environment


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


type Binds a = [(FBind a)]

type ContT a m c = ((c -> m a) -> m a)

type UnifyResult a =
  Maybe ( Binds a
        , Substitution Name a
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

data Atom n a = AVar Name | AUni Integer | ACtr Text a | AInd n a [(Text, a)] -- | AImplAbs n a a 
  deriving Eq

data Spine n a = Spine (Atom n a) [(ArgType, a)]


type Atom'             = Atom Name InternalCore
type Spine'            = Spine Name InternalCore
type Binds'            = Binds InternalCore
type FBind'            = FBind InternalCore
type Formula'          = Formula Name InternalCore
type UnifyResult'      = UnifyResult InternalCore
--type FlatFormula'      = Formula (Core AnnBind Name χ)
type Substitution'     = Substitution Name InternalCore
type SingleConstraint' = SingleConstraint InternalCore

makeLenses ''FlatFormula
makeLenses ''FBind

instance Eq (FBind a) where
  b == b' = b^.elem_name == b'^.elem_name

instance (Subst Name s a) => Subst Name s (FBind a) where
  substitute shadow sub (FBind quant name ty) = 
    FBind quant name (substitute (Set.insert name shadow) sub ty) 

  free_vars (FBind _ nm et) = Set.delete nm $ free_vars et 
    
instance (Pretty n, Pretty a) => Pretty (Spine n a) where
  pretty (Spine a vs) = pretty a <+> "|" <+> pretty vs

instance Pretty a => Pretty (FBind a) where
  pretty (FBind q n ty) = pretty q <+> pretty n <+> "⮜" <+> pretty ty

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

instance (Pretty a, Pretty n) => Pretty (Atom n a) where 
  pretty (AVar v) = pretty v
  pretty (AUni i) = pretty ((Uni i) :: InternalCore)
  pretty (ACtr label ty) = "(" <> pretty label <+> "﹨" <+> pretty ty <> ")"
  pretty (AInd name kind ctors) =
    vsep [ "μ" <+> pretty name <+> "⮜" <+> pretty kind <+> "."
         , indent 2 (align (vsep $ map (\(text, ty) -> pretty text <+> pretty ty) ctors)) ]

instance AlphaEq Name a => AlphaEq Name (Atom Name a) where
  αequal rename l r = case (l,r) of 
    (AVar n, AVar n') -> 
      case bimap (Map.lookup n) (Map.lookup n') rename of
        (Just (Just r), Just (Just r')) -> r == n' && r' == n
        (Nothing, Nothing) -> n == n'
        _ -> False
    (AUni i, AUni i') -> i == i'
    (ACtr label ty, ACtr label' ty') -> label == label' && αequal rename ty ty'
    _ -> False


{---------------------------- TOP-LEVEL UNIFICATION ----------------------------}
{- The solve function is the top-level procedure, and the driver is the        -}
{- uni_while function. This will perform successive transformations until a    -}
{- formula is in 'solved form'.                                                -}
{-                                                                             -}
{- This unification algorithm only works for those formulas which are in a     -}
{- known to be decidable. All other forms will return an ambiguous constraint  -}
{- error.                                                                      -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


solve :: forall err m. (MonadError err m, MonadGen m, Alternative m) => (SigilDoc -> err) -> CanonEnv m -> Formula' -> m Substitution'
solve liftErr env = let ?lift_err = liftErr in solve' env

solve' :: forall err m. (MonadError err m, MonadGen m, Alternative m, ?lift_err :: (SigilDoc -> err))
  => CanonEnv m -> Formula' -> m Substitution'
solve' _ = fmap fst . (\v -> uni_while (v^.binds) mempty (v^.constraints)) . flatten where

  uni_while :: Binds' -> Substitution' -> [SingleConstraint'] -> m (Substitution', [SingleConstraint'])
  uni_while quant_vars sub cs = 
    let -- uni_with :: (MonadError (SigilDoc) m, MonadReader (Env' χ) m) => (SingleConstraint' χ -> ContT b m (UnifyResult' χ))
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
  check_finished cs = throw ("ambiguous constraints: " <> pretty cs)

  unify_one :: Binds' -> SingleConstraint' -> ContT r m UnifyResult'
  unify_one binds constraint cont = case constraint of 
    a :≗: b -> do
      c' <- unify_eq binds a b
      case c' of 
        Nothing -> cont =<< unify_eq binds b a
        r -> cont r
    _ -> cont Nothing
  
  unify_search :: Binds' -> SingleConstraint' -> ContT r m UnifyResult'
  unify_search binds constraint cont = case constraint of
    a :∈: b | not_universe b -> right_search binds a b cont
    _ -> cont Nothing
    where 
      not_universe (Uni _) = False
      not_universe _ = True
  
  unify_search_atom :: Binds' ->  SingleConstraint' -> ContT r m UnifyResult'
  unify_search_atom binds constraint cont = case constraint of
    a :∈: b -> right_search binds a b cont
    _ -> cont Nothing
  
  -- new_cont cont out = case out of
  --   Just (quant_vars', cons') -> Just (quant_vars', mempty, cons')
      

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


unify_eq :: forall m err. (MonadError err m, MonadGen m, ?lift_err :: SigilDoc -> err) =>
  Binds' -> InternalCore -> InternalCore -> m UnifyResult'
unify_eq quant_vars a b = case (a, b) of 
  -- (Coreχ χ, Coreχ χ') ->
  --   if χ == χ' then
  --     pure $ Just (quant_vars, mempty, [])
  --   else
  --     throwError ("unequal Coreχ values" :: SigilDoc)
  (Uni n, Uni n') ->
    if n == n' then
      pure $ Just (quant_vars, mempty, [])
    else throw ("unequal universes:"
                <+> "(𝕌 " <> pretty n <> ")"
                <+> "and"
                <+> "(𝕌 " <> pretty n' <> ")")

  (s, s') | αeq s s' -> pure $ Just (quant_vars, mempty, [])

  -- (Var χ n, Var χ' n') -> check quantification
  -- (Prd _ (AnnBind (n, a)) b, Prd _ (AnnBind (n', a')) b') -> 
  --   pure $ Just (add_bind Forall a, [(a :≗: a'), (b :≗: b')], id)

  -- TODO: this is not in Caledon!!! do we have a case prd-prd or prd-any or any-prd??? 
  (Prd i (AnnBind (n, ty)) body, Prd i' (AnnBind (n', ty')) body') | i == i' -> 
    pure $ Just (add_bind Forall n ty quant_vars, mempty, [(ty :≗: ty'), (body :≗: subst (n' ↦ Var n) body')])

  -- Case Lam-Lam
  (Abs i (AnnBind (n, ty)) body, Abs i' (AnnBind (n', ty')) body') | i == i' -> 
    pure $ Just (add_bind Forall n ty quant_vars, mempty, [(ty :≗: ty'), (body :≗: subst (n' ↦ Var n) body')])

  -- Case Lam-Any (both left and right variants)
  (s, Abs Regular (AnnBind (n, ty)) body) -> 
    pure $ Just (add_bind Forall n ty quant_vars, mempty, [s :≗: app Regular body (Var n)])
  (Abs Regular (AnnBind (n, ty)) body, s) -> 
    pure $ Just (add_bind Forall n ty quant_vars, mempty, [app Regular body (Var n) :≗: s])


  -- Note: original was matching with spine, meaning it may include more than
  -- just App (e.g. vars, ∀, ...)
  (s, s') -> do
    (Spine atom terms) <- case (unwind s) of
      Just v -> pure v
      _ -> throw $ vsep ["unwinding failed for term:" <+> pretty s, "unifying for equality to:" <+> pretty s']
    mbind <- get_elem atom quant_vars
    case mbind of
      Left bind | bind^.elem_quant == Exists -> do
        let ty = bind^.elem_type
            var = bind^.elem_name
            fors = Set.fromList $ get_foralls_after var quant_vars
            exists = Set.fromList $ get_exists_after var quant_vars
        case unwind s' of
          Just (Spine atom' terms') -> do
            mbind' <- get_elem atom' quant_vars
            case mbind' of 
              Right ty' ->
                if all_elements_are_consts fors (fmap snd terms)
                then gvar_const (var, terms, ty) (atom', terms', ty')
                else pure Nothing
              Left (FBind { _elem_quant=Forall, _elem_type=ty', _elem_name=var' })
                | (not $ elem (Var var) (fmap snd terms)) && Set.member var' fors ->
                  if not $ is_partial_perm fors (fmap snd terms)
                  then pure Nothing
                  else throw "gvar-uvar depends"
                | Set.member var (free_vars (fmap snd terms')) ->
                  if not $ is_partial_perm fors (fmap snd terms)
                  then pure Nothing
                  else throw "occurs check failed"
                | Set.member var' fors ->
                  if is_partial_perm fors (fmap snd terms)
                  then gvar_uvar_inside (var, terms, ty) (var', terms', ty')
                  else throw "occurs check failed"
                | otherwise ->
                  if all_elements_are_consts fors (fmap snd terms)
                  then gvar_uvar_outside (var, terms, ty) (var', terms', ty')
                  else throw "occurs check failed"
              Left bind'@(FBind { _elem_quant=Exists, _elem_type=ty', _elem_name=var'}) ->
                if not $ is_partial_perm fors (fmap snd terms) && is_partial_perm fors (fmap snd terms') && Set.member var' exists
                then pure Nothing
                else if var == var'
                  then gvar_gvar_same (var, terms, ty) (var', terms', ty')
                  else if Set.member var (free_vars (fmap snd terms'))
                    then throw "occurs check failed"
                    else gvar_gvar_diff bind (var, terms, ty) (var', terms', ty') bind'
          _ -> pure Nothing -- gvar-gvar same
    
      -- In this case, mbind is either
      -- A universally bound variable
      -- A type constant (universe/inductive type)
      _ -> case unwind s' of
        Just (Spine atom' _) | not (αeq atom atom') -> do
          mbind' <- get_elem atom' quant_vars
          case mbind' of 
            Left bind' | bind'^.elem_quant == Exists -> pure $ Nothing
            _ -> throw ("can't unify two different universal equalities:"
                        <+> pretty atom <+> "and" <+> pretty atom')
      
        -- uvar-uvar! In this case, we need only check that 
        Just (Spine atom' terms') | αeq atom atom' -> do
          let -- TODO: Confirm that match is correct (I just kinda made it up..)
            match ((at, a):al) ((at', b):bl)
              | at == at'      = ((a :≗: b) :) <$> match al bl 
              | at == Implicit = match al ((at', b) : bl)
              | otherwise      = match ((at, a) : al) bl 
            match [] [] = return []
            match _ _ = throw "different numbers of arguments"
      
          constraints <- match terms terms'
          pure $ Just (quant_vars, mempty, constraints)
        _ -> throw ("can't unify a ∀-var against a term")

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
    -- This case matches with the GVar-Uvar Outside case from the paper
    -- M has the form c M₁ … Mₘ for a constant c: (v₁:B₁) → … (vₙ:Bₙ) → B.
    -- here, we perform an imitation: let 
    --   L = λ [u₁:A₁ … uₙ:Aₙ] (c (x₁ u₁ … uₙ) … (xₘ u₁ … uₙ))
    -- Then, we transition to
    --   ∃x₁: (u₁:A₁) → (uₙ:Aₙ) → B₁ ...
    --     ∃xₘ: (u₁:A₁) → (uₙ:Aₙ) → [(xₘ₋₁ u₁ … uₙ/v₁) … (x₁ u₁ … uₙ/vₘ)] Bₘ ...
    --       [L/x]F
    -- 
    -- Imitations are performed by the gvar_fixed helper function, meaning
    -- gvar_const doesn't have to do much work!
    -- TODO: change arg type to (Atom, [InternalCore], InternalCore)
    gvar_const :: (Name, [(ArgType, InternalCore)], InternalCore) -> (Atom', [(ArgType, InternalCore)], InternalCore) -> m (UnifyResult')
    gvar_const a@(_, _, _) b@(atom, _, _) =
      gvar_fixed a b $ const (unatom atom)

    -- GVar-Uvar Onside
    -------------------
    -- Same as GVar-Const (see above)
    gvar_uvar_outside :: (Name, [(ArgType, InternalCore)], InternalCore) -> (Name, [(ArgType, InternalCore)], InternalCore) -> m UnifyResult'
    gvar_uvar_outside l r = gvar_const l ((_1 %~ AVar) r)

    -- GVar-Uvar Inside
    -------------------
    --   M has the form y
    --
    gvar_uvar_inside :: (Name, [(ArgType, InternalCore)], InternalCore) -> (Name, [(ArgType, InternalCore)], InternalCore) -> m UnifyResult'
    gvar_uvar_inside a@(_, terms, _) b@(var', _, _) = 
      case elem_index (Var var') $ (reverse . fmap snd) terms of
        Nothing -> pure Nothing
        Just i -> gvar_fixed a ((_1 %~ AVar) b) $ Var . (!! i) 

    -- GVar-Gvar Same
    -----------------
    -- M has the form xyψ(1)…yψ(n). For some permutation ψ. Then, pick the
    -- unique permutation ρ with ρ(k) = ψ(i) for all i such that ψ(i) = ϕ(i)
    -- Perform an imitation:
    --
    -- Then, let L = λ [u₁:A₁ … uₙ:Aₙ] (x' uₚ(1) … uₚ(n)) and transition to
    --    ∃x':(u₁:Aρ(1) → ... → uₙ:Aρ(n) → A) [L/x:Tₓ]Γ,x':Tₓ F
    --
    gvar_gvar_same :: (Name, [(ArgType, InternalCore)], InternalCore) -> (Name, [(ArgType, InternalCore)], InternalCore) -> m UnifyResult'
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
            lbody = wind (Spine (AVar var) (fmap (\(at,nm,_) -> (at, Var nm)) perm))

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
    gvar_gvar_diff :: FBind' -> (Name, [(ArgType, InternalCore)], InternalCore) -> (Name, [(ArgType, InternalCore)], InternalCore) -> FBind' -> m UnifyResult'
    gvar_gvar_diff top (var, terms, ty) (var', terms', _) binder =
      raise_to_top top binder (var', terms') $ \b subO -> do
        let a = (var, over (mapped._2) (subst subO) terms, subst subO ty)
        gvar_gvar_diff' a b

    -- See gvar_gvar_diff for more details. In short, this performs a set of 
    -- raising operations on the binding `bind'  
    raise_to_top :: FBind' -> FBind' -> (Name, [(ArgType, InternalCore)]) -> ((Name, [(ArgType, InternalCore)], InternalCore) -> Substitution' -> m UnifyResult') -> m UnifyResult'
    raise_to_top top binder sp m | are_adjacent top binder quant_vars =
      m (fst sp, snd sp, binder^.elem_type) mempty
    raise_to_top top binder sp m = do
      x' <- freshen (binder^.elem_name)
      let hl = reverse $ get_binds_between top binder quant_vars

          newx_args = map ((Regular,) . Var . view elem_name) hl 

          sub = (binder^.elem_name) ↦ wind (Spine (AVar x') newx_args)

          -- TOOD: make sure the use of regular here 
          ty' = untelescope_type (map (\fb -> (Regular, fb^.elem_name, fb^.elem_type)) hl, binder^.elem_type)

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

      result <- add_sub =<< m (fst sp, over (mapped._2) (subst sub) (snd sp), ty') sub
      pure $ fmap (\(quant_vars, sub, cons) -> (remove_var x' $ update_binds quant_vars, sub, cons)) result

    -- See gvar_gvar_diff for more details
    gvar_gvar_diff' :: (Name, [(ArgType, InternalCore)], InternalCore) -> (Name, [(ArgType, InternalCore)], InternalCore)-> m UnifyResult'
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
            (i',_) <- filter (\(_,y') -> y == y') $ zip bbindings terms' 
            pure (iyt,i')

          l = untelescope (abindings, wind (Spine (AVar new_var) (fmap (\((at,nm,_),_) -> (at, Var nm)) perm)))
          l' = untelescope (bbindings, wind (Spine (AVar new_var) (fmap (\(_,(at,nm,_)) -> (at, Var nm)) perm)))

          newty = untelescope_type (map fst perm, get_base n ty) 

          sub = (var' ↦ l') <> (var ↦ l)

          quant_vars' = remove_var var $
                        remove_var var' $
                        add_before var Exists new_var newty $ quant_vars


        in pure $ Just (quant_vars', sub, [] {- var xN :@: xNty] -} )

    -- GVar-Fixed
    -----------------
    -- Recall, formula has form:
    --     … ∃x: (u₁:A₁ → … → uₙ:Aₙ → A) … ∀y₁:B₁…yₙ:Bₙ .
    --         x yϕ(1) … yϕ(n) ≗ M
    --
    -- While not a specific rule in itself, Gvar-fixed is useful as helper when
    -- M has the form c M₁ … Mₙ for a fixed c, (constant/universally quantified)
    -- c : (v₁:B₁) → … (vₘ:Bₘ) → B.
    -- here, we perform an imitation: let 
    --   L = λ [u₁:A₁ … uₙ:Aₙ] (c (x₁ u₁ … uₙ) … (xₘ u₁ … uₙ))   x ↦ :succ @xm  :succ :zero
    -- Then, we transition to
    --   ∃x₁: (u₁:A₁) → (uₙ:Aₙ) → B₁ ...
    --     ∃xₘ: (u₁:A₁) → (uₙ:Aₙ) → [(xₘ₋₁ u₁ … uₙ/v₁) … (x₁ u₁ … uₙ/vₘ)] Bₘ ...
    --       [L/x]F
    -- 
    gvar_fixed :: (Name, [(ArgType, InternalCore)], InternalCore) -> (Atom', [(ArgType, InternalCore)], InternalCore) -> ([Name] -> InternalCore) -> m UnifyResult'
    gvar_fixed (var, terms, ty) (atom, terms', ty') action = do
      let get_tybinds = fst . telescope_type

          aₙₛ = get_tybinds ty  -- The bindings u₁:A₁ … uₙ:Aₙ annotated by their implicitness
          bₘₛ = get_tybinds ty' -- The bindings v₁B₁ … vₙ:Bₙ annotated by their implicitness

      -- TOOD: confirm below is true: consider use in toLTerm?
      -- the vector of bindings x₁: (u₁:A₁) → … (uₙ:Aₙ) → B, …,
      --   xₘ (∪_1:A₁) → … (uₙ:Aₙ) → [(xₘ₋₁ u₁ … uₙ/v₁) … (x₁ u₁ … uₙ/vₘ)]B
      xₘₛ <- forM bₘₛ $ \(at, _, _) -> do
        x <- fresh_varn "@xm-"
        pure $ (at, x, wind (Spine (AVar x) (map (\(at, n, _) -> (at, Var n)) aₙₛ)))

      let to_l_term term = case term of
              Prd at bind body -> Abs at bind $ to_l_term body
              _ -> foldl (\v' (at, v) -> app at v' v) (action $ fmap (view _2) aₙₛ) $ fmap (\(x,_,y) -> (x,y)) xₘₛ
          -- The term L, which we will substitute for x
          l = to_l_term ty

          vbuild e = untelescope_type (aₙₛ, e)

          -- produce the set of substitutions starting at [] and ending with
          -- [(xₘ₋₁ u₁ … uₙ/v₁) … (x₁ u₁ -- … uₙ/vₘ)] m, which can then be
          -- applied to B (see transition in description)
          subst_bty :: Substitution' -> InternalCore -> [(ArgType, Name, InternalCore)] -> m [(Name, InternalCore)]
          subst_bty sub term l = case (term,l) of 
            (Prd _ b ty, (_, x, xi):xmr) -> -- TODO: check to make sure impl-prod isn't a special case
              (:) (x, vbuild $ subst sub (snd $ unann b))
                <$> (subst_bty (Sub.insert (aname b) xi sub) ty xmr)
            (_, []) -> pure []
            _ -> throw "_ is not well typed for _ on _"

          sub = var ↦ l

      quant_vars' <- subst sub
        <$> remove_var var
        <$> foldr ($) quant_vars
        <$> fmap (\(n, ty) -> add_after var Exists n ty)
        <$> (subst_bty mempty ty' xₘₛ)

      pure $ Just ( quant_vars'
                  , sub
                  -- application of sub to wind (var, terms) seems to be related
                  -- to a bug in HOU.hs (Caledon)
                  , [subst sub (wind (Spine (AVar var) terms)) :≗: wind (Spine atom terms')])


    -------------------------------- Predicates ---------------------------------
    -- These functions correspond to particular properties of an object(s)

    -- TODO: account for inductive values
    -- Returns true if the second argument is a partial permutation of the first
    is_partial_perm :: Set Name -> [InternalCore] -> Bool
    is_partial_perm fors = go mempty where
      go _ [] = True
      go s (Var n : rest) =
         Set.member n fors && not (Set.member n s) && go s rest
      go _ _ = False

    -- Returns true if the second argument consists solely of 'constant' unchanging
    -- values (i.e. ∀-bound vars, type universes or inductive values).
    -- The set is assumed to contain universally quantified variables.  
    -- TODO: there /might/ be a bug if an inductive value uses an inner ∃-bound var??
    all_elements_are_consts :: Set Name -> [InternalCore] -> Bool
    all_elements_are_consts fors = go where
      go [] = True
      go (Var n : vars) = Set.member n fors && go vars
      go (Uni _ : vars) = go vars
      go (Ctr _ _ : vars) = go vars
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
  
right_search :: forall m err r. (MonadError err m, MonadGen m, Alternative m, ?lift_err :: SigilDoc -> err) =>
  Binds' -> InternalCore -> InternalCore -> ContT r m UnifyResult'
right_search quant_vars val goal cont = 
  case goal of 
    -- Rule G Π: M ∈ (x:A) → B ⇒ ∀x: A.∃y: B.(y ≗ M x) ∧ y ∈ B
    Prd Regular (AnnBind(n,a)) b -> do
      x <- fresh_varn "@sx-"
      y <- fresh_varn "@sy-"
      let b' = subst (n ↦ Var x) b
      -- TODO: make sure order is correct!
      let quant_vars' = add_bind Exists y b' $ add_bind Forall x a quant_vars
      cont $ Just (quant_vars', mempty, [Var y :≗: (app Regular val (Var x)), Var y :∈: b'])

    _ -> case unwind goal of
      -- G Atom 1 / G Atom 2
      -- ∀x:A. F[M ∈ C] ⇒ ∀x:A. F[x ∈ A >> M ∈ C]
      --       F[M ∈ C] ⇒ ∀x:A. F[c₀ ∈ A >> M ∈ C]
      -- For C an atomic type (i.e. inductive/universe, not product!)
      -- for c₀ a constant of that type.
      Just (Spine atom _) ->  do
        -- Step 1: get the fixed type of the atom. This means return nothing if
        -- the atom is an existentially bound variable.
        --atom_elem <- get_elem atom quant_vars
        val_target <- case unwind val of 
              Just (Spine v _) -> do
                elem <- get_elem v quant_vars
                case elem of 
                  Left (FBind { _elem_quant=Forall, _elem_type=ty }) -> pure $ Just (unatom v, ty)
                  Right ty -> pure $ Just (unatom v, ty)
                  _ -> pure Nothing
              Nothing -> pure Nothing
        

        let ind_targets :: Atom' -> [(InternalCore, InternalCore)]
            ind_targets = \case
              (AInd nm sort ctors) -> flip map ctors $ \(label, ctorty) ->
                let ty = Ind nm sort ctors
                in (Ctr label ty, subst (nm ↦ ty) ctorty)
              _ -> []

        let same_family (FBind {_elem_type = ty}) = 
              case unwind ty of 
                Just (Spine atom' _) -> αeq atom atom'
                Nothing -> False
      
              
        targets <- case val_target of
          Just t -> pure [t]
          Nothing -> 
            let foralls = filter ((== Forall) . view elem_quant) quant_vars
            in pure $ ind_targets atom
               <> fmap (\v -> (Var (view elem_name v), view elem_type v))
                    (filter same_family foralls)

        -- targets <- case atom of
        --   (AInd nm sort ctors) -> pure $ flip map ctors $ \(label, ctorty) ->
        --     let ty = Ind nm sort ctors
        --     in (Ctr label ty, subst (nm ↦ ty) ctorty)
        --   (AVar nm) -> (nm ! quant_vars) >>= \case
        --     (FBind { _elem_quant=Forall, _elem_type=ty }) -> pure [(Var nm, ty)]
        --     _ -> pure []
        --   _ -> throw "couldn't get targets..."

            -- TODO: not 100% sure this is what the search wanted
            -- The targets are formed by the list of value-constructors for the
            -- type?
            -- targets take the form (ctor, ctorty)
            -- possibly also other forms??
            -- targets = case atom_ty of
            --   Just ty@(Ind nm _ ctors) -> flip map ctors $ \(label, ctorty) -> 
            --     (Ctr label ty, subst (nm ↦ ty) ctorty)
            --   Just t -> [(unatom atom, t)]
            --   Nothing -> [] -- TODO: this is WRONG BIG WRONG!

        
        let is_fixed nm =
              case List.find (\v -> ((nm ==) . _elem_name) v
                          && ((Forall ==) ._elem_quant) v) quant_vars of 
                Just _ -> True
                Nothing -> False
        if all is_fixed (free_vars val <> free_vars goal)
        -- If there are no existentials in the value or the goal, then we are
        -- done!
        then cont $ Just (quant_vars, mempty, [])
        -- Otherwise
        else case targets of 
          [] -> cont $ Nothing
          _ -> inter quant_vars [] targets
            where
              inter _ [] [] = throw "No More Options"
              inter _ cg [] = asum (reverse cg)
              inter qvs cg (t : ts) = do
                -- TODO: it's very important we get the threading of quant_vars
                -- correct here. It may be that we are supposed to 'reset' each time
                -- we left-search (as we explore different branches...)
                (qvs',cs) <- left_search qvs t (val, goal)
                -- TODO: ensure that we assumed correctly the value sequ=False
                -- (for HOU.hs)
                inter qvs (cont (Just (qvs', mempty, cs)) : cg) ts
        
      Nothing -> throw ("can't: right-search with goal (empty unwind):" <> pretty goal)

    
-- left search solves constraints of the form A ∈ T >> B ∈ T', roughly meaning
-- "If A inhabits T then B inhabits T'"
-- these constraints are generated as part of the right_search, but are not
-- directly available in formulas.
left_search :: forall m err. (MonadError err m, MonadGen m, ?lift_err :: SigilDoc -> err) =>
  Binds' -> (InternalCore, InternalCore) -> (InternalCore, InternalCore) -> m (Binds', [SingleConstraint'])
left_search quant_vars (x, target) (m, goal) = left_cont quant_vars x target
  where
    left_cont quant_vars val target = case target of
      -- Rule D Π:
      --   F[N ∈ (x:A) → B >> M ∈ C] → F[∃x:A . (N x ∈ B >> M ∈ C) ∧ x ∈ A]
      Prd Regular (AnnBind (nm, a)) b -> do
        x' <- fresh_var "@sla"
        let quant_vars' = add_bind Exists x' a quant_vars
        (quant_vars'', cons) <- left_cont quant_vars' (app Regular val (Var x')) (subst (nm ↦ Var x') b)
        pure $ (quant_vars'', cons <> [Var x' :∈: a])
      Abs Regular _ _ -> throw ("λ does not represent a type" <> pretty target)
      -- Rule D Atom:
      --   F[N ∈ A N₁ … Nₙ >> a M₁ … M] → F[N₁ ≗ M₁ ∧ … ∧ Nₙ ≗ Mₙ ∧ N ≗ M]
      _ -> pure $ (quant_vars, [goal :≗: target, m :≗: val])

{------------------------------ BINDING FUNCTIONS ------------------------------}
{- These are functions to adjust bindings in flat formulas.                    -}
{- add : Add a binding at the lowest level                                     -}
{-------------------------------------------------------------------------------}

(!) :: (MonadError err m, ?lift_err :: SigilDoc -> err) => Name -> (Binds InternalCore) -> m (FBind InternalCore)
name ! (b:bs)
  | b^.elem_name == name = pure $ b
  | otherwise = name ! bs
name ! [] = throw $ "Couldn't find binding: " <+> pretty name

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

-- TODO This is being used in place of add_to_tail. Might be bad/wrong!!
-- possibly should be adding bind at end!
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

unatom :: Atom' -> InternalCore
unatom atom = case atom of
  AVar n -> Var n
  AUni n -> Uni n
  ACtr label ty -> Ctr label ty
  AInd nm kind ctors -> Ind nm kind ctors


get_elem :: (MonadError err m, ?lift_err :: SigilDoc -> err) =>
  Atom' -> Binds' -> m (Either FBind' InternalCore)
get_elem atom quant_vars = case atom of
  AVar n -> Left <$> n ! quant_vars
  AUni n -> pure $ Right (Uni (n+1))
  AInd _ k _ -> pure $ Right k
  ACtr label ty -> case ty of
    Ind nm _ ctors -> case List.find ((== label) . view _1) ctors of 
      Just (_, ctorty) -> pure $ Right (subst (nm ↦ ty) ctorty) -- TODO: possibly ACtr label ty
      Nothing -> throw "badly formed constructor"
    _ -> throw "constructor should have inductive type"

unwind :: InternalCore -> Maybe Spine'
unwind core = fmap (uncurry Spine) (go [] core)
  where 
    go :: [(ArgType, InternalCore)] -> InternalCore -> Maybe (Atom', [(ArgType, InternalCore)])
    go as = \case
      App at l r -> go ((at,r):as) l
      Var n -> Just (AVar n, as)
      Uni n -> Just (AUni n, as)
      Ctr label ty -> Just (ACtr label ty, as)
      Ind nm kind ctors -> Just (AInd nm kind ctors, as)
      _ -> Nothing

wind :: Spine' -> InternalCore
wind (Spine a vars) = foldl (\l (at, r) -> App at l r) (unatom a) vars

-- For now, we don't need rebuild spine, as only atoms are allowed to be at the
-- head of a spine.
-- rebuild_spine :: Spine' 
    
untelescope :: ([(ArgType, Name, InternalCore)], InternalCore) -> InternalCore
untelescope (bindings, body) = foldr (\(at, n, ty) -> Abs at (AnnBind (n, ty))) body bindings

telescope_type :: InternalCore -> ([(ArgType, Name, InternalCore)], InternalCore)
telescope_type term = case term of
  Prd at (AnnBind (n, ty)) b -> (_1 %~ (:) (at, n, ty)) $ telescope_type b
  a -> ([], a)

untelescope_type :: ([(ArgType, Name, InternalCore)], InternalCore) -> InternalCore
untelescope_type (bindings, ty) = foldr (\(at, nm, rt) -> Prd at (AnnBind (nm, rt))) ty bindings
  
flatten :: Formula Name a -> FlatFormula a
flatten formula = case formula of
  Conj cs -> FlatFormula [] cs
  And l r -> flatten l <> flatten r
  Bind q n ty f -> (binds %~ (:) (FBind q n ty)) $ flatten f 

get_base :: Int -> InternalCore -> InternalCore 
get_base 0 a = a                            
get_base n (Abs _ _ r) = get_base (n - 1) r
get_base _ a = a



{------------------------------- MISC. INSTANCES -------------------------------}

throw :: (MonadError err m, ?lift_err :: SigilDoc -> err) => SigilDoc -> m a
throw doc = throwError $ ?lift_err doc

-- Helper functions that maybe can be moved to another file??  

app :: ArgType -> InternalCore -> InternalCore -> InternalCore  
app at val arg = case val of 
  Abs _ (AnnBind (n, _)) e -> subst ((n ↦ arg) :: Substitution') e
  _ -> App at val arg 

aname :: AnnBind n b -> n
aname (AnnBind (n, _)) = n

