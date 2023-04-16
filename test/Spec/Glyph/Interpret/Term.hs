module Spec.Glyph.Interpret.Term (term_spec) where

import Control.Monad.Except hiding (void)
import Data.Text (Text)

import Prettyprinter
import Prettyprinter.Render.Glyph

import Glyph.Abstract.Environment
import Glyph.Abstract.Syntax
import Glyph.Concrete.Typed
import Glyph.Interpret.Term

import TestFramework

term_spec :: TestGroup
term_spec = TestGroup "term" $ Left [norm_spec, eq_spec]

eq_spec :: TestGroup
eq_spec = TestGroup "αβη-equivalence" $ Right eq_tests

norm_spec :: TestGroup
norm_spec = TestGroup "normalization" $ Right norm_tests

type NormM a = Except (Doc GlyphStyle) a

runNormM :: NormM a -> Either (Doc GlyphStyle) a
runNormM = runExcept

default_env :: Env (Maybe TypedCore, TypedCore)
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
    eq_test :: Text -> TypedCore -> TypedCore -> TypedCore -> Bool -> Test
    eq_test name ty l r expected = 
      Test name $ case runNormM $ equiv default_env ty l r of 
        Right b | b == expected -> Nothing
                | otherwise -> Just "eq-test error: term equality different to expected"
        Left e -> Just $ "equiv failed - message:" <+> e
  

norm_tests :: [Test]            
norm_tests =
  [ -- 𝒰 → 𝒰
    norm_test "𝒰0-const" (𝓊 1) (𝓊 0) (𝓊 0)

    -- (λ (A:𝒰₁) A) 𝒰 → 𝒰
  , norm_test "id-app" (𝓊 1) (([(idn 0 "A", 𝓊 1)] ⇒ idv 0 "A") ⋅ 𝓊 0) (𝓊 0)

  ]
  
  where
    norm_test :: Text -> TypedCore -> TypedCore -> TypedCore -> Test
    norm_test name ty a expected = 
      Test name $ case runNormM $ normalize default_env ty a of 
        Right result | result == expected -> Nothing
                     | otherwise -> Just "norm-test error: result different to value"
        Left e -> Just $ "normalization err:" <+> e

-- var :: n -> Core b n UD
-- var = Var void

𝓊 :: Int -> TypedCore
𝓊 = Uni ()

(⇒) :: [(Name, TypedCore)] -> TypedCore -> TypedCore
args ⇒ body = foldr (\var body -> Abs () (AnnBind var) body) body args

(→) :: [(Name, TypedCore)] -> TypedCore -> TypedCore
args → body = foldr (\var body -> Prd () (AnnBind var) body) body args

(⋅) :: TypedCore -> TypedCore -> TypedCore
(⋅) = App ()

idv :: Integer -> Text -> TypedCore
idv n t = Var () $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)

-- qvar :: Text -> Core AnnBind Name UD
-- qvar v = Var void $ Name $ Left [v]
