module Spec.Glyph.Abstract.AlphaEq (alphaeq_spec) where

import Data.Text (Text)

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment
import Glyph.Abstract.AlphaEq

import TestFramework
import Spec.Glyph.Abstract.CoreUD


alphaeq_spec :: TestGroup
alphaeq_spec = TestGroup "α-eq" $ Right alphaeq_tests

-- TODO: test with AnnBind also 
type CoreUD = Core OptBind Name UD
type DefinitionUD = Definition OptBind Name UD

alphaeq_tests :: [Test]
alphaeq_tests =
  -- Testing Core for Alpha Equality
  [ eq_test "simple-eq" (𝓊 0) (𝓊 0) True
  , eq_test "simple-neq" (𝓊 0) (𝓊 1) False

  , eq_test "free-eq" (idv 0 "x") (idv 0 "x") True
  , eq_test "free-neq" (idv 1 "y") (idv 0 "x") False

  , eq_test "lam-eq" ([idn 0 "x"] ⇒ idv 0 "x") ([idn 0 "x"] ⇒ idv 0 "x") True
  , eq_test "lam-renamed-eq" ([idn 0 "x"] ⇒ idv 0 "x") ([idn 1 "y"] ⇒ idv 1 "y") True
  , eq_test "lam-free-neq" ([idn 0 "x"] ⇒ idv 1 "y") ([idn 1 "y"] ⇒ idv 1 "y") False

  , eq_test "prd-eq" ([idn 0 "x"] → idv 0 "x") ([idn 0 "x"] → idv 0 "x") True
  , eq_test "prd-renamed-eq" ([idn 0 "x"] → idv 0 "x") ([idn 1 "y"] → idv 1 "y") True
  , eq_test "prd-free-neq" ([idn 0 "x"] → idv 1 "y") ([idn 1 "y"] → idv 1 "y") False

  , eq_test "def-eq" (idn 0 "x" ≜ 𝓊 0) (idn 0 "x" ≜ 𝓊 0) True
  , eq_test "def-neq" (idn 0 "x" ≜ 𝓊 0) (idn 0 "x" ≜ 𝓊 1) False
  -- Testing Definitions for Alpha Equality
  ]

  where 
    eq_test :: AlphaEq n a => Text -> a -> a -> Bool -> Test
    eq_test name a b eq  
      | αeq a b == eq = Test name Nothing 
      | eq            = Test name $ Just "terms are supposed to be α-equal"
      | otherwise     = Test name $ Just "terms are not supposed to not α-equal"

𝓊 :: Int -> CoreUD
𝓊 = Uni void

(⇒) :: [Name] -> CoreUD -> CoreUD
args ⇒ body = foldr (\var body -> Abs void (OptBind (Just var, Nothing)) body) body args

(→) :: [Name] -> CoreUD -> CoreUD
args → body = foldr (\var body -> Prd void (OptBind (Just var, Nothing)) body) body args

-- (⋅) :: Core b n UD -> Core b n UD -> Core b n UD
-- (⋅) = App void

idv :: Integer -> Text -> CoreUD
idv n t = Var void $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)

(≜) :: Name -> CoreUD -> DefinitionUD
n ≜ val = Mutual [(OptBind (Just n, Nothing), val)]
