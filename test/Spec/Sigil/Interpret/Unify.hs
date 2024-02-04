module Spec.Sigil.Interpret.Unify (unify_spec) where

import Prelude hiding (lookup)
import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Map as Map

import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Unify
import Sigil.Abstract.Names
import Sigil.Abstract.AlphaEq
import Sigil.Abstract.Substitution
import Sigil.Concrete.Internal
import Sigil.Concrete.Decorations.Implicit
import Sigil.Interpret.Unify
import Sigil.Interpret.Canonical.Environment (CanonEnv(..))

import TestFramework


canon_empty :: CanonEnv m 
canon_empty = CanonEnv Map.empty Map.empty Map.empty

unify_spec :: TestGroup
unify_spec = TestGroup "unify" $ Right unify_tests

type UnifyM a = ExceptT (Doc SigilStyle) Gen a

runUnifyM :: Integer -> UnifyM a -> Either (Doc SigilStyle) a
runUnifyM n = run_gen_from n . runExceptT

unify_tests :: [Test]     
unify_tests = 
  [ eq_test "universe-eq" (𝓊 0) (𝓊 0) True
  , eq_test "universe-¬eq" (𝓊 1) (𝓊 0) False

  , eq_test "id-fn-eq"
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ (idv 1 "x"))
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ (idv 1 "x"))
    True

  , eq_test "id-var-eq" (idv 1 "x") (idv 1 "x") True
  , eq_test "id-var-neq" (idv 1 "x") (idv 2 "y") False

  , eq_test "id-αrenamed-eq"
    ([(idn 0 "A", 𝓊 0), (idn 2 "x", idv 0 "A")] ⇒ (idv 2 "x"))
    ([(idn 0 "A", 𝓊 0), (idn 3 "y", idv 0 "A")] ⇒ (idv 3 "y"))  
    True

  , eq_test "prod-eq"
    ([(idn 0 "A", 𝓊 0)] → idv 0 "A")
    ([(idn 0 "A", 𝓊 0)] → idv 0 "A")  
    True

  , eq_test "prod-α-eq"
    ([(idn 0 "A", 𝓊 0)] → idv 0 "A")
    ([(idn 1 "B", 𝓊 0)] → idv 1 "B")
    True

  -- TODO: ambiguous constraint - is this correct?
  -- ∃x:𝕌. ∃y:𝕌 . x ≗ y
  , can_solve_test "ex-var1"
    (Bind Exists (idn 0 "x") (𝓊 0) $
       Bind Exists (idn 1 "y") (𝓊 0) $ Conj [idv 0 "x" :≗: idv 1 "y"])
    False

  -- ∀x:𝕌. ∃y:𝕌 . x ≗ y
  , can_solve_test "ex-var1"
    (Bind Forall (idn 0 "x") (𝓊 0) $
       Bind Exists (idn 1 "y") (𝓊 0) $ Conj [idv 0 "x" :≗: idv 1 "y"])
    True

  -- ∃x:𝕌. ∀y:𝕌 . x ≗ y 
  , can_solve_test "ex-var1"
    (Bind Forall (idn 0 "x") (𝓊 0) $
       Bind Exists (idn 1 "y") (𝓊 0) $ Conj [idv 0 "x" :≗: idv 1 "y"])
    False -- THIS SHOULD FAIL!!!

  -- ∃x:(A:𝕌→𝕌). x ≗ λ [A:𝕌] A
  , can_solve_test "ex-lam" (Bind Exists (idn 0 "x") ([(idn 1 "A", 𝓊 0)] → 𝓊 0) $
                            Conj [idv 0 "x" :≗: ([(idn 1 "A", 𝓊 0)] ⇒ idv 1 "A")]) True


  -- ∃ x ⮜ ℕ. x ≃ two
  -- x ↦ two
  , let nat = Ind (idn 1 "N") (𝓊 0) [("zero", idv 1 "N"), ("succ", [(idn 2 "_", idv 1 "N")] → idv 1 "N")]
    in solve_test "ex-two"
        (Bind Exists (idn 0 "x") nat $ Conj [idv 0 "x" :≗: (Ctr "succ" nat ⋅ (Ctr "succ" nat ⋅ Ctr "zero" nat))])
        [(idn 0 "x", (Ctr "succ" nat ⋅ (Ctr "succ" nat ⋅ Ctr "zero" nat)))]

  -- ∃ x ⮜ ℕ. x ∈ ℕ
  -- x ↦ zero
  , let nat = Ind (idn 1 "N") (𝓊 0) [("zero", idv 1 "N"), ("succ", [(idn 2 "_", idv 1 "N")] → idv 1 "N")]
    in solve_test "inhabit-nat"
        (Bind Exists (idn 0 "x") nat $ Conj [idv 0 "x" :∈: nat])
        [(idn 0 "x", Ctr "zero" nat)]

  -- ∃ x ⮜ ℕ. two + x ≅ four
  -- , let nat = Ind (idn 1 "N") (𝓊 0) [("zero", idv 1 "N"), ("succ", [(idn 2 "_", idv 1 "N")] → idv 1 "N")]
  --   in solve_test "ex-add"
  --       (Bind Exists (idn 0 "n") nat $ Conj [idv 0 "n" :∈: nat])
  --       (idn 0 "n" ↦ Ctr "zero" nat)
  -- TODO: add test testing this:
  -- ∃ x ⮜ ℕ. two + x ≅ four

  -- Currently, this fails with an occurs check
  -- this is technically 'correct' behaviour (as per the caledon operational semantics) (I think)
  -- however, it might be nice if we could fix that
  -- for id ≜ (A ⮜ 𝕌) → (v ⮜ A) → A, ∃ x ⮜ id. x ∈ id
  -- x ↦ λ (A ⮜ 𝕌) (v ⮜ A) → v
  -- , let id = [(idn 0 "A", 𝓊 0), (idn 1 "v", idv 0 "A")] → idv 0 "A"
  --   in solve_test "inhabit-id"
  --       (Bind Exists (idn 2 "x") id $ Conj [idv 2 "x" :∈: id])
  --       [(idn 2 "x", ([(idn 0 "A", 𝓊 0), (idn 1 "v", idv 0 "A")] ⇒ idv 1 "v"))]
  ]

  where 
    eq_test :: Text -> InternalCore -> InternalCore -> Bool -> Test
    eq_test name l r b = 
      Test name $ case runUnifyM 10 $ solve id canon_empty (Conj [l :≗: r]) of 
        Right _ | b == True -> Nothing
                | otherwise -> Just "unify-eq succeded when expecting fail"
        Left e  | b == False -> Nothing
                | otherwise -> Just $ "unify failed - message:" <+> e

    can_solve_test :: Text -> Formula Name InternalCore -> Bool -> Test
    can_solve_test name formula b =
      Test name $ case runUnifyM 10 $ solve id canon_empty formula of 
        Right _ | b == True -> Nothing
                | otherwise -> Just "unify-eq succeded when expecting fail"
        Left e  | b == False -> Nothing
                | otherwise -> Just $ "unify failed - message:" <+> e

    solve_test :: Text -> Formula Name InternalCore -> [(Name, InternalCore)] -> Test
    solve_test name formula sub =
      Test name $ case runUnifyM 10 $ solve id canon_empty formula of 
        Right s
          | s `has` sub -> Nothing
          | otherwise -> Just $ vsep ["Incorrect substitution.", "Got:" <+> pretty s, "Expecting it to have:" <+> pretty sub]
        Left e -> Just $ "solve failed - message:" <+> e

    has :: Substitution Name InternalCore -> [(Name, InternalCore)] -> Bool 
    has s sub = foldr (\(k, v) t -> t && maybe False (αeq v) (lookup k s)) True sub 


-- var :: n -> Core b n UD
-- var = Var void

𝓊 :: Integer -> InternalCore
𝓊 = Uni

(⇒) :: [(Name, InternalCore)] -> InternalCore -> InternalCore
args ⇒ body = foldr (\var body -> Abs Regular (AnnBind var) body) body args

(→) :: [(Name, InternalCore)] -> InternalCore -> InternalCore
args → body = foldr (\var body -> Prd Regular (AnnBind var) body) body args

(⋅) :: InternalCore -> InternalCore -> InternalCore
(⋅) = App

idv :: Integer -> Text -> InternalCore
idv n t = Var $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)

-- qvar :: Text -> Core AnnBind Name UD
-- qvar v = Var void $ Name $ Left [v]
