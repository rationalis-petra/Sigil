module Spec.Sigil.Interpret.Term (term_spec) where

import Control.Monad.Except
import Data.Text (Text)

import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Environment
import Sigil.Concrete.Internal
import Sigil.Concrete.Decorations.Implicit
import Sigil.Interpret.Term

import TestFramework

term_spec :: TestGroup
term_spec = TestGroup "term" $ Left [norm_spec, eq_spec]

eq_spec :: TestGroup
eq_spec = TestGroup "αβη-equivalence" $ Right eq_tests

norm_spec :: TestGroup
norm_spec = TestGroup "normalization" $ Right norm_tests

type NormM a = ExceptT (Doc SigilStyle) Gen a

runNormM :: NormM a -> Either (Doc SigilStyle) a
runNormM = run_gen . runExceptT

default_env :: Env (Maybe InternalCore, InternalCore)
default_env = env_empty

eq_tests :: [Test]     
eq_tests = 
  [ eq_test "universe-eq" (𝓊 1) (𝓊 0) (𝓊 0) True
  , eq_test "universe-¬eq" (𝓊 2) (𝓊 1) (𝓊 0) False

  , eq_test "id-eq"
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] → (idv 0 "A"))
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ (idv 1 "x"))
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ (idv 1 "x"))
    True

  , eq_test "id-αrenamed-eq"
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] → (idv 0 "A"))
    ([(idn 0 "A", 𝓊 0), (idn 2 "x", idv 0 "A")] ⇒ (idv 2 "x"))
    ([(idn 0 "A", 𝓊 0), (idn 2 "x", idv 0 "A")] ⇒ (idv 2 "x"))  
    True

  , eq_test "id-2αrenamed-eq"
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] → (idv 0 "A"))
    ([(idn 0 "A", 𝓊 0), (idn 2 "x", idv 0 "A")] ⇒ (idv 2 "x"))
    ([(idn 0 "A", 𝓊 0), (idn 3 "y", idv 0 "A")] ⇒ (idv 3 "y"))  
    True

  , eq_test "id-2αrenamed-eq"
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] → (idv 0 "A"))
    ([(idn 0 "A", 𝓊 0), (idn 2 "x", idv 0 "A")] ⇒ (idv 2 "x"))
    ([(idn 0 "A", 𝓊 0), (idn 3 "y", idv 0 "A")] ⇒ (idv 3 "y"))  
    True
  ]

  where 
    eq_test :: Text -> InternalCore -> InternalCore -> InternalCore -> Bool -> Test
    eq_test name ty l r expected = 
      Test name $ case runNormM $ equiv id default_env ty l r of 
        Right b | b == expected -> Nothing
                | otherwise -> Just "eq-test error: term equality different to expected"
        Left e -> Just $ "equiv failed - message:" <+> e
  

norm_tests :: [Test]            
norm_tests =
  [ -- 𝕌 ↦ 𝕌
    norm_test "𝕌0-const" (𝓊 1) (𝓊 0) (𝓊 0)

    -- (λ (A:𝕌₁) A) 𝕌 ↝ 𝕌
  , norm_test "id-app" (𝓊 1) (([(idn 0 "A", 𝓊 1)] ⇒ idv 0 "A") ⋅ 𝓊 0) (𝓊 0)

    -- (A:𝕌₀) → 𝕌₀ ↝ (A:𝕌₀) → 𝕌₀
  , norm_test "pi-const" (𝓊 0) ([(idn 0 "A", 𝓊 0)] → 𝓊 0) ([(idn 0 "A", 𝓊 0)] → 𝓊 0)

  ]
  
  where
    norm_test :: Text -> InternalCore -> InternalCore -> InternalCore -> Test
    norm_test name ty a expected = 
      Test name $ case runNormM $ normalize id default_env ty a of 
        Right result | result == expected -> Nothing
                     | otherwise ->
                         Just $ vsep [ "norm-test error: result different to value."
                                     , "result:" <+> pretty result 
                                     , "expected:" <+> pretty expected
                                     ] 
        Left e -> Just $ "normalization err:" <+> e

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
