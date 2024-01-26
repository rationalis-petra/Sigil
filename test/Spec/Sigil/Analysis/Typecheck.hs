{-# LANGUAGE ImplicitParams #-}
module Spec.Sigil.Analysis.Typecheck (type_spec) where

import Control.Monad.Except
import Control.Lens (view, _1, _2)
import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as Map

import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Environment
import Sigil.Concrete.Internal
import Sigil.Concrete.Decorations.Implicit
import Sigil.Analysis.Typecheck
import qualified Sigil.Interpret.Canonical.Term as Term
import Sigil.Interpret.Canonical.Values

import TestFramework

-- TODO: check typed output!

type_spec :: TestGroup
type_spec = TestGroup "typing" $ Left [check_spec, infer_spec]

check_spec :: TestGroup
check_spec = TestGroup "type-checking" $ Right check_tests

infer_spec :: TestGroup
infer_spec = TestGroup "type-inference" $ Right infer_tests

type CheckM = ExceptT (Doc SigilStyle) Gen

runCheckM :: CheckM a -> Either (Doc SigilStyle) a
runCheckM = run_gen . runExceptT 
-- fmap (\(x,_) -> x) (global_env canon)
-- data CheckInterp m err env = CheckInterp
--   { normalize :: (SigilDoc -> err) -> env -> InternalCore -> InternalCore -> m InternalCore
--   , αβη_eq :: (SigilDoc -> err) -> env -> InternalCore -> InternalCore -> InternalCore -> m Bool
--   , lift_err :: TCErr -> err
--   }

type TestEnv = ( Map UniqueName (Sem CheckM, InternalCore, InternalCore)
               , Map Path (Sem CheckM, InternalCore, InternalCore) )

to_semenv :: TestEnv -> SemEnv CheckM
to_semenv (l1, l2) = (fmap (view _1) l1, fmap (view _1) l2, Map.empty)

test_interp :: CheckInterp CheckM SigilDoc TestEnv
test_interp = CheckInterp
  { normalize = \lift_err env -> Term.normalize lift_err (to_semenv env)
  , αβη_eq = \lift_err env -> Term.equiv lift_err (to_semenv env)
  , lift_err = spretty
  }

default_env :: Env TestEnv CheckM
default_env = Env
  { i_lookup = \(Name n) (e1, e2) -> case n of
      Right un -> pure $ fmap (view _2) (Map.lookup un e1)
      Left qn -> pure $ fmap (view _2) (Map.lookup qn e2)
  , i_insert = \(Name n) (mval, ty) (e1, e2) -> case n of
      Left qn -> throwError $ ("Cannot insert qualified name:" <+> pretty qn)
      Right un -> do
        let sem_env = (fmap (\(x,_,_) -> x) e1, fmap (\(x,_,_) -> x) e2, Map.empty)
        (val', sem) <- case mval of
          Just v -> (v, ) <$> let ?lift_err = id in Term.eval v sem_env
          Nothing -> (Var (Name n), ) . flip Neutral (NeuVar (Name n)) <$> let ?lift_err = id in Term.eval ty sem_env
        pure $ (Map.insert un (sem, val', ty) e1, e2)

  , i_insert_path = \n (val, ty) (e1, e2) -> do
      let sem_env = (fmap (\(x,_,_) -> x) e1, fmap (\(x,_,_) -> x) e2, Map.empty)
      sem <- let ?lift_err = id in Term.eval val sem_env
      pure $ (e1, Map.insert n (sem, val, ty) e2)
  , i_impl = (Map.empty, Map.empty)
  }

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
      Test name $ case runCheckM $ check test_interp default_env term ty of 
        Right _
          | succ -> Nothing
          | otherwise -> Just "checker passed, expected to fail"
        Left e
          | not succ -> Nothing
          | otherwise -> Just $ "checker failed, err:" <+> e
  

infer_tests :: [Test]            
infer_tests =
  [ -- 𝕌 : 𝕌1
    infer_test "𝕌₀-𝕌₁" (𝓊 0) (𝓊 1)

  , infer_test "simple-lam" ([(idn 0 "A", 𝓊 0)] ⇒ idv 0 "A") ([(idn 0 "_", 𝓊 0)] → 𝓊 0)

  , infer_test "multi-lam-1"
    ([(idn 0 "A", 𝓊 0), (idn 1 "B", 𝓊 0)] ⇒ idv 1 "B")
    ([(idn 1 "_", 𝓊 0), (idn 0 "_", 𝓊 0)] → 𝓊 0)

  , infer_test "multi-lam-2"
    ([(idn 0 "A", 𝓊 0), (idn 1 "B", 𝓊 0)] ⇒ idv 0 "A")
    ([(idn 1 "_", 𝓊 0), (idn 0 "_", 𝓊 0)] → 𝓊 0)

  , infer_test "dep-lam"
    ([(idn 0 "A", 𝓊 0), (idn 1 "x", idv 0 "A")] ⇒ idv 1 "x")
    ([(idn 0 "A", 𝓊 0), (idn 0 "_", idv 0 "A")] → idv 0 "A")

  , infer_test "prd-cum"
    ([(idn 0 "A", 𝓊 0)] → idv 0 "A")
    (𝓊 1)
  ]
  
  where
    infer_test :: Text -> InternalCore -> InternalCore -> Test
    infer_test name term ty = 
      Test name $ case runCheckM $ infer test_interp default_env term of 
        Right (_, ty')
          | ty == ty' -> Nothing
          | otherwise -> Just $ "expected type:" <+> pretty ty <+> "got" <+> pretty ty'
        Left e -> Just $ "inference err:" <+> e

-- var :: n -> Core b n UD
-- var = Var void

𝓊 :: Integer -> InternalCore
𝓊 = Uni

(⇒) :: [(Name, InternalCore)] -> InternalCore -> InternalCore
args ⇒ body = foldr (\var body -> Abs Regular (AnnBind var) body) body args

(→) :: [(Name, InternalCore)] -> InternalCore -> InternalCore
args → body = foldr (\var body -> Prd Regular (AnnBind var) body) body args

-- (⋅) :: Core b n UD -> Core b n UD -> Core b n UD
-- (⋅) = App void

idv :: Integer -> Text -> InternalCore
idv n t = Var $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)

-- qvar :: Text -> Core AnnBind Name UD
-- qvar v = Var void $ Name $ Left [v]
