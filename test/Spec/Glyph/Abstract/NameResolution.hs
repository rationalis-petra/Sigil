module Spec.Glyph.Abstract.NameResolution (resolve_spec) where

import Prelude hiding (putStrLn)
import Data.Text (Text)

import Prettyprinter
import Prettyprinter.Render.Glyph

import TestFramework
import Glyph.Abstract.Environment
import Glyph.Abstract.Syntax
import Glyph.Abstract.NameResolution

import Spec.Glyph.Abstract.CoreUD

resolve_spec :: TestGroup
resolve_spec = TestGroup "name-resolution" $ Right tests

res_test :: Text -> Core OptBind Text UD -> Core OptBind Name UD -> Test
res_test name val result = Test name err where
  err =
    if run_gen (resolve val) /= result then
      Just $ print_bad val result
    else
      Nothing

  print_bad :: Core OptBind Text UD -> Core OptBind Name UD -> Doc GlyphStyle
  print_bad l r = pretty l <+> "is does not resolve to " <+> pretty r

tests :: [Test]
tests =
  [ res_test "free-var" (var "x") (qvar "x")
  , res_test "abs-bound-var" (["y"] ⇒ (var "y")) ([idn 0 "y"] ⇒ (idv 0 "y"))
  , res_test "free-bound-mixed" (["y"] ⇒ (var "x")) ([idn 0 "y"] ⇒ (qvar "x"))
  , res_test "2-bound-var" (["y", "x"] ⇒ (var "y" ⋅ var "x")) ([idn 0 "y", idn 1 "x"] ⇒ (idv 0 "y" ⋅ idv 1 "x"))

  , res_test "abs-bound-ty-var" ([("y", 𝓊 0)] =⇒ (var "y")) ([(idn 0 "y", 𝓊 0)] =⇒ (idv 0 "y"))

  , res_test "prd-bound-var" (["y"] → (var "y")) ([idn 0 "y"] → (idv 0 "y"))
  , res_test "prd-bound-ty-var" ([("y", 𝓊 0)] -→ (var "y")) ([(idn 0 "y", 𝓊 0)] -→ (idv 0 "y"))
  ]
  where
    var :: n -> Core b n UD
    var = Var void

    𝓊 :: Int -> Core b n UD
    𝓊 = Uni void

    (⇒) :: [n] -> Core OptBind n UD -> Core OptBind n UD
    args ⇒ body = foldr (\var body -> Abs void (OptBind $ Left var) body) body args

    (=⇒) :: [(n, Core OptBind n UD)] -> Core OptBind n UD -> Core OptBind n UD
    args =⇒ body = foldr (\var body -> Abs void (OptBind $ Right var) body) body args

    (→) :: [n] -> Core OptBind n UD -> Core OptBind n UD
    args → body = foldr (\var body -> Prd void (OptBind $ Left var) body) body args

    (-→) :: [(n, Core OptBind n UD)] -> Core OptBind n UD -> Core OptBind n UD
    args -→ body = foldr (\var body -> Prd void (OptBind $ Right var) body) body args

    (⋅) :: Core b n UD -> Core b n UD -> Core b n UD
    (⋅) = App void

    idv :: Integer -> Text -> Core OptBind Name UD
    idv n t = Var void $ Name $ Right (n, t)

    idn :: Integer -> Text -> Name
    idn n t = Name $ Right (n, t)

    qvar :: Text -> Core OptBind Name UD
    qvar v = Var void $ Name $ Left [v]
  

