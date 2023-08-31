module Spec.Sigil.Analysis.Typecheck (type_spec) where

import Control.Monad.Except hiding (void)
import Data.Text (Text)

import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Environment
import Sigil.Concrete.Internal
import Sigil.Analysis.Typecheck
import Sigil.Interpret.Term

import TestFramework

-- TODO: check typed output!


type_spec :: TestGroup
type_spec = TestGroup "typing" $ Left [check_spec, infer_spec]

check_spec :: TestGroup
check_spec = TestGroup "type-checking" $ Right check_tests

infer_spec :: TestGroup
infer_spec = TestGroup "type-inference" $ Right infer_tests

type CheckM a = ExceptT (Doc SigilStyle) Gen a

runCheckM :: CheckM a -> Either (Doc SigilStyle) a
runCheckM = run_gen . runExceptT 

default_env :: Env (Maybe InternalCore, InternalCore)
default_env = env_empty

check_tests :: [Test]     
check_tests = 
  [ check_test "universe-sub" (𝓊 0) (𝓊 1) True
  , check_test "universe-super" (𝓊 2) (𝓊 1) False

  , check_test "id-eq"
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ (idv 1 "x"))
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] → (idv 0 "A"))
    True

  , check_test "id-αrenamed-eq"
    ([(idn 0 "A", 𝓊 0), (idn 2 "x", idv 0 "A")] ⇒ (idv 2 "x"))
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] → (idv 0 "A"))
    True

  , check_test "id-2αrenamed-eq"
    ([(idn 0 "A", 𝓊 0), (idn 2 "x", idv 0 "A")] ⇒ (idv 2 "x"))
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] → (idv 0 "A"))
    True
  ]

  where 
    check_test :: Text -> InternalCore -> InternalCore -> Bool -> Test
    check_test name term ty succ = 
      Test name $ case runCheckM $ check normalize default_env term ty of 
        Right _
          | succ -> Nothing
          | otherwise -> Just "checker passed, expected to fail"
        Left e
          | not succ -> Nothing
          | otherwise -> Just $ "checker failed, err:" <+> e
  

infer_tests :: [Test]            
infer_tests =
  [ -- 𝒰 : 𝒰1
    infer_test "𝒰0-𝒰1" (𝓊 0) (𝓊 1)

  , infer_test "simple-lam" ([(idn 0 "A", 𝓊 0)] ⇒ idv 0 "A") ([(idn 0 "A", 𝓊 0)] → 𝓊 0)

  , infer_test "multi-lam-1"
    ([(idn 0 "A", 𝓊 0), (idn 1 "B", 𝓊 0)] ⇒ idv 1 "B")
    ([(idn 0 "A", 𝓊 0), (idn 1 "B", 𝓊 0)] → 𝓊 0)

  , infer_test "multi-lam-2"
    ([(idn 0 "A", 𝓊 0), (idn 1 "B", 𝓊 0)] ⇒ idv 0 "A")
    ([(idn 0 "A", 𝓊 0), (idn 1 "B", 𝓊 0)] → 𝓊 0)

  , infer_test "dep-lam"
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ idv 1 "x")
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] → idv 0 "A")

  , infer_test "prd-cum"
    ([(idn 0 "A", 𝓊 0)] → idv 0 "A")
    (𝓊 1)
  ]
  
  where
    infer_test :: Text -> InternalCore -> InternalCore -> Test
    infer_test name term ty = 
      Test name $ case runCheckM $ infer normalize default_env term of 
        Right (_, ty')
          | ty == ty' -> Nothing
          | otherwise -> Just $ "expected type:" <+> pretty ty <+> "got" <+> pretty ty'
        Left e -> Just $ "inference err:" <+> e

-- var :: n -> Core b n UD
-- var = Var void

𝓊 :: Int -> InternalCore
𝓊 = Uni

(⇒) :: [(Name, InternalCore)] -> InternalCore -> InternalCore
args ⇒ body = foldr (\var body -> Abs (AnnBind var) body) body args

(→) :: [(Name, InternalCore)] -> InternalCore -> InternalCore
args → body = foldr (\var body -> Prd (AnnBind var) body) body args

-- (⋅) :: Core b n UD -> Core b n UD -> Core b n UD
-- (⋅) = App void

idv :: Integer -> Text -> InternalCore
idv n t = Var $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)

-- qvar :: Text -> Core AnnBind Name UD
-- qvar v = Var void $ Name $ Left [v]
