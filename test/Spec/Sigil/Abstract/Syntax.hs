module Spec.Sigil.Abstract.Syntax (syntax_spec) where

import Data.Text (Text)
import Data.Bifunctor (bimap)

import Prettyprinter
import Prettyprinter.Render.Text 

import Sigil.Abstract.Syntax  
import Sigil.Abstract.Environment  

import TestFramework
import Spec.Sigil.Abstract.CoreUD


syntax_spec :: TestGroup
syntax_spec = TestGroup "syntax" $ Left [pretty_group]

-- TODO: 
-- Test pretty-printing
-- Test equality
pretty_group :: TestGroup
pretty_group = TestGroup "pretty" $ Right
  [ pretty_test "universe" (𝓊 0) "𝕌₀"
  , pretty_test "var" (idv 0 "hello") "hello"
  , pretty_test "app" (𝓊 0 ⋅ idv 0 "hello") "𝕌₀ hello"
  , pretty_test "telescope" (𝓊 0 ⋅ 𝓊 1 ⋅ idv 0 "hello") "𝕌₀ 𝕌₁ hello"
  , pretty_test "nested-app" (𝓊 0 ⋅ (𝓊 1 ⋅ idv 0 "hello")) "𝕌₀ (𝕌₁ hello)"
  , pretty_test "abs" (just_vars [idn 0 "x"] ⇒ idv 0 "x") "λ x → x"
  , pretty_test "abs-tel" (just_vars [idn 0 "x"] ⇒ (idv 0 "x" ⋅ idv 0 "x")) "λ x → (x x)"
  , pretty_test "abs-tel" (just_vars [idn 0 "x", idn 1 "y"] ⇒ (idv 0 "x" ⋅ idv 0 "x")) "λ x y → (x x)"
  , pretty_test "prd" (just_vars [idn 0 "A"] → (idv 0 "A")) "(A ⮜ _) → A"
  , pretty_test "prd" (just_vars [idn 0 "A", idn 0 "B"] → (idv 0 "A")) "(A ⮜ _) → (B ⮜ _) → A"
  , pretty_test "prd" (just_types [idv 0 "A"] → (idv 0 "A")) "A → A"
  , pretty_test "prd" (just_types [idv 0 "A", idv 1 "B"] → (idv 0 "A")) "A → B → A"
  , pretty_test "prd" (both_vt [(idn 0 "A", 𝓊 0)] → (idv 0 "A")) "(A ⮜ 𝕌₀) → A"
  , pretty_test "prd" (both_vt [(idn 0 "A", 𝓊 0), (idn 1 "B", idv 0 "A")] → (idv 0 "A")) "(A ⮜ 𝕌₀) → (B ⮜ A) → A"
  ]
  where
    pretty_test :: Text -> CoreUD -> Text -> Test
    pretty_test name term expected
      | pptext (pretty term) == expected = Test name Nothing
      | otherwise = Test name $ Just $
          "expected" <+> pretty expected <+> "got" <+> pretty term

    pptext :: Doc ann -> Text
    pptext = renderStrict . layoutPretty defaultLayoutOptions


𝓊 :: Integer -> CoreUD
𝓊 = Uniχ void

idv :: Integer -> Text -> CoreUD
idv n t = Varχ void $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)

(⋅) :: CoreUD -> CoreUD -> CoreUD
(⋅) = Appχ void

(⇒) :: [(Maybe Name, Maybe CoreUD)] -> CoreUD -> CoreUD
args ⇒ body = foldr (\bind body -> Absχ void (OptBind bind) body) body args

(→) :: [(Maybe Name, Maybe CoreUD)] -> CoreUD -> CoreUD
args → body = foldr (\bind body -> Prdχ void (OptBind bind) body) body args

just_vars :: [Name] -> [(Maybe Name, Maybe CoreUD)]
just_vars = fmap ((,Nothing) . Just)

just_types :: [CoreUD] -> [(Maybe Name, Maybe CoreUD)]
just_types = fmap ((Nothing,) . Just)

both_vt :: [(Name, CoreUD)] -> [(Maybe Name, Maybe CoreUD)]
both_vt = fmap $ bimap Just Just
