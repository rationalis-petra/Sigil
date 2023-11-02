module Spec.Sigil.Interpret.Substitution (subst_spec) where

import Data.Text (Text)
import Data.Set (fromList)

import Prettyprinter

import Sigil.Abstract.Names
import Sigil.Abstract.Substitution
import Sigil.Concrete.Internal

import TestFramework

subst_spec :: TestGroup
subst_spec = TestGroup "substitution" $ Left [fv_group, subst_group]

subst_group :: TestGroup  
subst_group = TestGroup "substitution" $ Right subst_tests

subst_tests :: [Test]     
subst_tests = 
  [ subst_test "empty-subst" empty (𝓊 0) (𝓊 0)
  , subst_test "single-var" (idn 0 "x" ↦ 𝓊 0) (idv 0 "x") (𝓊 0)

  , subst_test "under-abs" (idn 2 "y" ↦ 𝓊 0)
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ idv 2 "y")
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ 𝓊 0)

  , subst_test "shadowed-by-abs" (idn 2 "x" ↦ 𝓊 0)
    ([(idn 0 "A", 𝓊 0), (idn 2 "x", idv 0 "A")] ⇒ idv 2 "x")
    ([(idn 0 "A", 𝓊 0), (idn 2 "x", idv 0 "A")] ⇒ idv 2 "x")  
  ]

  where 
    subst_test :: Text -> Substitution Name InternalCore -> InternalCore -> InternalCore -> Test
    subst_test name sub term expected = Test name $
      let result = subst sub term  in
        if result == expected then
          Nothing
        else
          Just $ "expected:" <+> pretty expected <+> "got:" <+> pretty result


fv_group :: TestGroup  
fv_group = TestGroup "free-vars" $ Right fv_tests

fv_tests :: [Test]     
fv_tests = 
  [ fv_test "universe-empty" [] (𝓊 0)

  , fv_test "fn-captuerd" []
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ (idv 1 "x"))
  , fv_test "fn-free"
    [idn 2 "y"]
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ (idv 2 "y"))

  , fv_test "var" [idn 1 "x"] (idv 1 "x") 
  ]

  where 
    fv_test :: Text -> [Name] -> InternalCore -> Test
    fv_test name names term 
      | (free_vars term) == (fromList names) = Test name Nothing
      | otherwise = Test name $ Just "free-vars test failed"

𝓊 :: Integer -> InternalCore
𝓊 = Uni

(⇒) :: [(Name, InternalCore)] -> InternalCore -> InternalCore
args ⇒ body = foldr (\var body -> Abs (AnnBind var) body) body args

idv :: Integer -> Text -> InternalCore
idv n t = Var $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)
