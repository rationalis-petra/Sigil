{-# OPTIONS_GHC -XTypeOperators #-}
module Spec.Sigil.Analysis.NameResolution (resolve_spec) where

import Prelude hiding (putStrLn)
import Control.Monad.Except (runExceptT)
import qualified Data.Map as Map
import Data.Text (Text)
import Data.Bifunctor

import Prettyprinter
import Prettyprinter.Render.Sigil

import TestFramework
import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Concrete.Parsed
import Sigil.Concrete.Resolved
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Decorations.Implicit
import Sigil.Analysis.NameResolution


resolve_spec :: TestGroup
resolve_spec = TestGroup "name-resolution" $ Right tests

res_test :: Text -> ParsedCore -> ResolvedCore -> Test
res_test name val result = Test name err where
  err =
    case run_gen (runExceptT $ resolve_closed id Map.empty val) of 
      Right result' -> case result' == result of
        True -> Nothing 
        False -> Just $ print_bad val result  
      Left err -> Just $ pretty err

  print_bad :: ParsedCore -> ResolvedCore -> Doc SigilStyle
  print_bad l r = pretty l <+> "is does not resolve to " <+> pretty r

res_fail_test :: Text -> ParsedCore -> Text -> Test
res_fail_test name val err_message = Test name err where
  err =
    case run_gen (runExceptT $ resolve_closed id Map.empty val) of 
      Right val -> Just $ "expecting error:" <+> pretty err_message <+> "but got value:"  <+> pretty val
      Left err -> case err == err_message of 
        True -> Nothing
        False -> Just $ "expecting error:" <+> pretty err_message <+> "but got error:"  <+> pretty err 

tests :: [Test]
tests =
  [ res_fail_test "free-var" (var "x") "x"
  , res_fail_test "free-bound-mixed" (["y"] ⇒ (var "x")) "x"

  , res_test "abs-bound-var" (["y"] ⇒ (var "y")) ([idn 0 "y"] ⇒ (idv 0 "y"))
  , res_test "2-bound-var" (["y", "x"] ⇒ (var "y" ⋅ var "x")) ([idn 0 "y", idn 1 "x"] ⇒ (idv 0 "y" ⋅ idv 1 "x"))

  , res_test "lam-bound-ty-var" ([("y", 𝓊 0)] =⇒ (var "y")) ([(idn 0 "y", 𝓊 0)] =⇒ (idv 0 "y"))
  , res_test "lam-dep-fn"
    ([("y", 𝓊 0), ("x", var "y")] =⇒ (var "x"))
    ([(idn 0 "y", 𝓊 0), (idn 1 "x", idv 0 "y")] =⇒ (idv 1 "x"))

  , res_test "prd-bound-var" (["y"] → (var "y")) ([idn 0 "y"] → (idv 0 "y"))
  , res_test "prd-bound-ty-var" ([("y", 𝓊 0)] -→ (var "y")) ([(idn 0 "y", 𝓊 0)] -→ (idv 0 "y"))
  ]
  where
    var :: Monoid (Varχ χ) => n -> Core b n χ
    var = Varχ mempty

    𝓊 :: Monoid (Uniχ χ) => Integer -> Core b n χ
    𝓊 = Uniχ mempty

    (⇒) :: (Absχ χ ~ (Range, ArgType)) => [n] -> Core OptBind n χ -> Core OptBind n χ
    args ⇒ body = foldr (\var body -> Absχ (mempty, Regular) (OptBind (Just var, Nothing)) body) body args

    (=⇒) :: (Absχ χ ~ (Range, ArgType)) => [(n, Core OptBind n χ)] -> Core OptBind n χ -> Core OptBind n χ
    args =⇒ body = foldr (\b body -> Absχ (mempty, Regular) (OptBind $ bimap Just Just b) body) body args

    (→) :: (Prdχ χ ~ (Range, ArgType)) => [n] -> Core OptBind n χ -> Core OptBind n χ
    args → body = foldr (\var body -> Prdχ (mempty, Regular) (OptBind (Just var, Nothing)) body) body args

    (-→) :: (Prdχ χ ~ (Range, ArgType)) => [(n, Core OptBind n χ)] -> Core OptBind n χ -> Core OptBind n χ
    args -→ body = foldr (\b body -> Prdχ (mempty, Regular) (OptBind $ bimap Just Just b) body) body args

    (⋅) :: (Appχ χ ~ (Range, ArgType)) => Core b n χ -> Core b n χ -> Core b n χ
    (⋅) = Appχ (mempty, Regular)

    idv :: Monoid (Varχ χ) => Integer -> Text -> Core OptBind Name χ
    idv n t = Varχ mempty $ Name $ Right (n, t)

    idn :: Integer -> Text -> Name
    idn n t = Name $ Right (n, t)

    -- qvar :: Forallχ Monoid χ => Text -> Core OptBind Name χ
    -- qvar v = Varχ mempty $ Name $ Left [v]
  
