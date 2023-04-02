module Spec.Glyph.Abstract.Unify (unify_spec) where

import Control.Monad.Except hiding (void)
import Data.Text (Text)

import Prettyprinter
import Prettyprinter.Render.Glyph

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment
--import Glyph.Abstract.Substitution
import Glyph.Abstract.Unify

import TestFramework
import Spec.Glyph.Abstract.CoreUD  

unify_spec :: TestGroup
unify_spec = TestGroup "unify" $ Right unify_tests

type UnifyM a = ExceptT (Doc GlyphStyle) Gen a

runUnifyM :: UnifyM a -> Either (Doc GlyphStyle) a
runUnifyM = run_gen . runExceptT

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

  -- ∃x:(A:𝒰→𝒰). x ≗ λ [A:𝒰] A
  , can_solve_test "app" (Bind Exists (idn 0 "x") ([(idn 1 "A", 𝓊 0)] → 𝓊 0) $
                            Conj [idv 0 "x" :≗: ([(idn 1 "A", 𝓊 0)] ⇒ idv 1 "A")]) True

  , can_solve_test "app" (Bind Exists (idn 0 "x") ([(idn 1 "A", 𝓊 0)] → 𝓊 0) $
                            Conj [idv 0 "x" :≗: ([(idn 1 "A", 𝓊 0)] ⇒ idv 1 "A")]) True
  ]

  where 
    eq_test :: Text -> Core AnnBind Name UD -> Core AnnBind Name UD -> Bool -> Test
    eq_test name l r b = 
      Test name $ case runUnifyM $ solve (Conj [l :≗: r]) of 
        Right _ | b == True -> Nothing
                | otherwise -> Just "unify-eq succeded when expecting fail"
        Left e  | b == False -> Nothing
                | otherwise -> Just $ "unify failed - message:" <+> e

    can_solve_test :: Text -> Formula (Core AnnBind Name UD) -> Bool -> Test
    can_solve_test name formula b =
      Test name $ case runUnifyM$ solve formula of 
        Right _ | b == True -> Nothing
                | otherwise -> Just "unify-eq succeded when expecting fail"
        Left e  | b == False -> Nothing
                | otherwise -> Just $ "unify failed - message:" <+> e

    -- solve_test :: Text -> Formula (Core AnnBind Name UD) -> Substitution (Core AnnBind Name UD) -> Test
    -- solve_test name formula sub =
    --   Test name $ case runUnifyM $ solve formula of 
    --     Right s
    --       | s == sub  -> Nothing
    --       | otherwise -> Just $ "incorrect substitution produced:" <+> pretty s <+> "expecting" <+> pretty sub
    --     Left e -> Just $ "solve failed - message:" <+> e


-- var :: n -> Core b n UD
-- var = Var void

𝓊 :: Int -> Core b n UD
𝓊 = Uni void

(⇒) :: [(n, Core AnnBind n UD)] -> Core AnnBind n UD -> Core AnnBind n UD
args ⇒ body = foldr (\var body -> Abs void (AnnBind var) body) body args

(→) :: [(n, Core AnnBind n UD)] -> Core AnnBind n UD -> Core AnnBind n UD
args → body = foldr (\var body -> Prd void (AnnBind var) body) body args

-- (⋅) :: Core b n UD -> Core b n UD -> Core b n UD
-- (⋅) = App void

idv :: Integer -> Text -> Core AnnBind Name UD
idv n t = Var void $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)

-- qvar :: Text -> Core AnnBind Name UD
-- qvar v = Var void $ Name $ Left [v]
