module Spec.Glyph.Analysis.NameResolution (resolve_spec) where

import Prelude hiding (putStrLn)
import Data.Text (Text)
import Data.Bifunctor

import Prettyprinter
import Prettyprinter.Render.Glyph

import TestFramework
import Glyph.Abstract.Environment
import Glyph.Abstract.Syntax
import Glyph.Concrete.Parsed
import Glyph.Concrete.Resolved
import Glyph.Analysis.NameResolution


resolve_spec :: TestGroup
resolve_spec = TestGroup "name-resolution" $ Right tests

res_test :: Text -> ParsedCore -> ResolvedCore -> Test
res_test name val result = Test name err where
  err =
    if run_gen (resolve val) /= result then
      Just $ print_bad val result
    else
      Nothing

  print_bad :: ParsedCore -> ResolvedCore -> Doc GlyphStyle
  print_bad l r = pretty l <+> "is does not resolve to " <+> pretty r

tests :: [Test]
tests =
  [ res_test "free-var" (var "x") (qvar "x")
  , res_test "abs-bound-var" (["y"] ⇒ (var "y")) ([idn 0 "y"] ⇒ (idv 0 "y"))
  , res_test "free-bound-mixed" (["y"] ⇒ (var "x")) ([idn 0 "y"] ⇒ (qvar "x"))
  , res_test "2-bound-var" (["y", "x"] ⇒ (var "y" ⋅ var "x")) ([idn 0 "y", idn 1 "x"] ⇒ (idv 0 "y" ⋅ idv 1 "x"))

  , res_test "lam-bound-ty-var" ([("y", 𝓊 0)] =⇒ (var "y")) ([(idn 0 "y", 𝓊 0)] =⇒ (idv 0 "y"))
  , res_test "lam-dep-fn"
    ([("y", 𝓊 0), ("x", var "y")] =⇒ (var "x"))
    ([(idn 0 "y", 𝓊 0), (idn 1 "x", idv 0 "y")] =⇒ (idv 1 "x"))

  , res_test "prd-bound-var" (["y"] → (var "y")) ([idn 0 "y"] → (idv 0 "y"))
  , res_test "prd-bound-ty-var" ([("y", 𝓊 0)] -→ (var "y")) ([(idn 0 "y", 𝓊 0)] -→ (idv 0 "y"))
  ]
  where
    var :: Forallχ Monoid χ => n -> Core b n χ
    var = Varχ mempty

    𝓊 :: Forallχ Monoid χ => Int -> Core b n χ
    𝓊 = Uniχ mempty

    (⇒) :: Forallχ Monoid χ => [n] -> Core OptBind n χ -> Core OptBind n χ
    args ⇒ body = foldr (\var body -> Absχ mempty (OptBind (Just var, Nothing)) body) body args

    (=⇒) :: Forallχ Monoid χ => [(n, Core OptBind n χ)] -> Core OptBind n χ -> Core OptBind n χ
    args =⇒ body = foldr (\b body -> Absχ mempty (OptBind $ bimap Just Just b) body) body args

    (→) :: Forallχ Monoid χ => [n] -> Core OptBind n χ -> Core OptBind n χ
    args → body = foldr (\var body -> Prdχ mempty (OptBind (Just var, Nothing)) body) body args

    (-→) :: Forallχ Monoid χ => [(n, Core OptBind n χ)] -> Core OptBind n χ -> Core OptBind n χ
    args -→ body = foldr (\b body -> Prdχ mempty (OptBind $ bimap Just Just b) body) body args

    (⋅) :: Forallχ Monoid χ => Core b n χ -> Core b n χ -> Core b n χ
    (⋅) = Appχ mempty

    idv :: Forallχ Monoid χ => Integer -> Text -> Core OptBind Name χ
    idv n t = Varχ mempty $ Name $ Right (n, t)

    idn :: Integer -> Text -> Name
    idn n t = Name $ Right (n, t)

    qvar :: Forallχ Monoid χ => Text -> Core OptBind Name χ
    qvar v = Varχ mempty $ Name $ Left [v]
  
