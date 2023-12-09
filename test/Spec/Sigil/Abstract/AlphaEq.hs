module Spec.Sigil.Abstract.AlphaEq (alphaeq_spec) where

import Data.Text (Text)

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.AlphaEq

import TestFramework
import Spec.Sigil.Abstract.CoreUD


alphaeq_spec :: TestGroup
alphaeq_spec = TestGroup "α-eq" $ Right alphaeq_tests

-- TODO: test with AnnBind also 

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

  , eq_test "eql-eq" (ι [] (𝓊 1) (𝓊 0) (𝓊 0)) (ι [] (𝓊 1) (𝓊 0) (𝓊 0)) True
  , eq_test "eql-neq" (ι [] (𝓊 1) (𝓊 0) (𝓊 0)) (ι [] (𝓊 1) (𝓊 0) (𝓊 1)) False
  , eq_test "eql-bnd-eq"
    (ι [(OptBind (Just (idn 0 "x"), Nothing), (𝓊 0))] (𝓊 0) (idv 0 "x") (idv 0 "x"))
    (ι [(OptBind (Just (idn 0 "y"), Nothing), (𝓊 0))] (𝓊 0) (idv 0 "y") (idv 0 "y")) True
  , eq_test "eql-bnd-2-eq"
    (ι [(OptBind (Just (idn 0 "x"), Just (𝓊 1, 𝓊 0, 𝓊 0)), (𝓊 0))] (𝓊 0) (idv 0 "x") (idv 0 "x"))
    (ι [(OptBind (Just (idn 0 "y"), Just (𝓊 1, 𝓊 0, 𝓊 0)), (𝓊 0))] (𝓊 0) (idv 0 "y") (idv 0 "y")) True
  , eq_test "eql-dap-eq"
    (ι [(OptBind (Just (idn 0 "x"), Just (𝓊 1, 𝓊 0, 𝓊 0)), ρ (𝓊 0))] (𝓊 0) (idv 0 "x") (idv 0 "x"))
    (ι [(OptBind (Just (idn 1 "y"), Just (𝓊 1, 𝓊 0, 𝓊 0)), ρ (𝓊 0))] (𝓊 0) (idv 1 "y") (idv 1 "y")) True

  , eq_test "def-eq" (idn 0 "x" ≜ 𝓊 0) (idn 0 "x" ≜ 𝓊 0) True
  , eq_test "def-neq" (idn 0 "x" ≜ 𝓊 0) (idn 0 "x" ≜ 𝓊 1) False

  , eq_test "mod-empty-eq"
    (modul (Path ["empty"]) [] [] [])
    (modul (Path ["empty"]) [] [] []) True

  , eq_test "mod-single-eq"
    (modul (Path ["empty"]) [] [] [idn 0 "x" ≜ 𝓊 0])
    (modul (Path ["empty"]) [] [] [idn 0 "x" ≜ 𝓊 0]) True

  , eq_test "mod-length-neq"
    (modul (Path ["empty"]) [] [] [idn 0 "x" ≜ 𝓊 0])
    (modul (Path ["empty"]) [] [] []) False

  , eq_test "mod-length-neq"
    (modul (Path ["empty"]) [] [] [])
    (modul (Path ["empty"]) [] [] [idn 0 "x" ≜ 𝓊 0]) False

  , eq_test "mod-single-neq"
    (modul (Path ["empty"]) [] [] [idn 0 "x" ≜ 𝓊 0])
    (modul (Path ["empty"]) [] [] [idn 0 "x" ≜ 𝓊 1]) False
  -- Testing Definitions for Alpha Equality
  ]

  where 
    eq_test :: AlphaEq n a => Text -> a -> a -> Bool -> Test
    eq_test name a b eq  
      | αeq a b == eq = Test name Nothing 
      | eq            = Test name $ Just "terms are supposed to be α-equal"
      | otherwise     = Test name $ Just "terms are not supposed to not α-equal"

𝓊 :: Integer -> CoreUD
𝓊 = Uniχ void

(⇒) :: [Name] -> CoreUD -> CoreUD
args ⇒ body = foldr (\var body -> Absχ void (OptBind (Just var, Nothing)) body) body args

(→) :: [Name] -> CoreUD -> CoreUD
args → body = foldr (\var body -> Prdχ void (OptBind (Just var, Nothing)) body) body args

ι :: [(OptBind Name (CoreUD, CoreUD, CoreUD), CoreUD)] -> CoreUD -> CoreUD -> CoreUD -> CoreUD
ι = Eqlχ void

ρ :: CoreUD -> CoreUD
ρ = Dapχ void []

-- (⋅) :: Core b n UD -> Core b n UD -> Core b n UD
-- (⋅) = App void

idv :: Integer -> Text -> CoreUD
idv n t = Varχ void $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)

(≜) :: Name -> CoreUD -> EntryUD
n ≜ val = Singleχ void (OptBind (Just n, Nothing)) val

modul :: Path -> [ImportDef] -> [ExportDef] -> [EntryUD] -> ModuleUD
modul = Module
