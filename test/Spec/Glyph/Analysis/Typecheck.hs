module Spec.Glyph.Analysis.Typecheck (type_spec) where

import Control.Monad.Except hiding (void)
import Data.Text (Text)
import qualified Data.Map as Map
import Data.Map (Map)

import Prettyprinter
import Prettyprinter.Render.Glyph

import Glyph.Abstract.Environment
import Glyph.Abstract.Syntax
import Glyph.Analysis.Typecheck

import TestFramework
import Spec.Glyph.Abstract.CoreUD  

type_spec :: TestGroup
type_spec = TestGroup "typing" $ Left [check_spec, infer_spec]

check_spec :: TestGroup
check_spec = TestGroup "type-checking" $ Right check_tests

infer_spec :: TestGroup
infer_spec = TestGroup "type-inference" $ Right infer_tests

type CheckM a = Except (Doc GlyphStyle) a

runCheckM :: CheckM a -> Either (Doc GlyphStyle) a
runCheckM = runExcept

default_env :: Map Integer (Core AnnBind Name UD)
default_env = Map.empty

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
    check_test :: Text -> Core AnnBind Name UD -> Core AnnBind Name UD -> Bool -> Test
    check_test name term ty succ = 
      Test name $ case runCheckM $ check default_env term ty of 
        Right ()
          | succ -> Nothing
          | otherwise -> Just "checker passed, expected to fail"
        Left e
          | not succ -> Nothing
          | otherwise -> Just $ "checker failed, err:" <+> e
  

infer_tests :: [Test]            
infer_tests =
  [ -- 𝒰 : 𝒰1
    infer_test "𝒰0-𝒰1" (𝓊 0) (𝓊 1)
  ]
  
  where
    infer_test :: Text -> Core AnnBind Name UD -> Core AnnBind Name UD -> Test
    infer_test name term ty = 
      Test name $ case runCheckM $ infer default_env term of 
        Right ty' | ty == ty' -> Nothing
                  | otherwise -> Just "type inference produced the wrong type!"
        Left e -> Just $ "inference err:" <+> e

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
