module Spec.Glyph.Abstract.Syntax (syntax_spec) where

import Data.Text (Text)

import Prettyprinter
import Prettyprinter.Render.Text 

import Glyph.Abstract.Syntax  
import Glyph.Abstract.Environment  

import TestFramework
import Spec.Glyph.Abstract.CoreUD


syntax_spec :: TestGroup
syntax_spec = TestGroup "syntax" $ Left [pretty_group]

-- TODO: 
-- Test pretty-printing
-- Test equality
pretty_group :: TestGroup
pretty_group = TestGroup "pretty" $ Right
  [ pretty_test "universe" (𝓊 0) "𝒰0"
  , pretty_test "var" (idv 0 "hello") "hello"
  , pretty_test "app" (𝓊 0 ⋅ idv 0 "hello") "𝒰0 hello"
  , pretty_test "telescope" (𝓊 0 ⋅ 𝓊 1 ⋅ idv 0 "hello") "𝒰0 𝒰1 hello"
  , pretty_test "nested-app" (𝓊 0 ⋅ (𝓊 1 ⋅ idv 0 "hello")) "𝒰0 (𝒰1 hello)"
  , pretty_test "abs" ([idn 0 "x"] ⇒ idv 0 "x") "λ [x] x"
  , pretty_test "abs-tel" ([idn 0 "x"] ⇒ (idv 0 "x" ⋅ idv 0 "x")) "λ [x] (x x)"
  , pretty_test "prd" ([idn 0 "A"] → (idv 0 "A")) "A → A"
  , pretty_test "prd" ([idn 0 "A", idn 0 "B"] → (idv 0 "A")) "A → B → A"
  ]
  where
    pretty_test :: Text -> CoreUD -> Text -> Test
    pretty_test name term expected
      | pptext (pretty term) == expected = Test name Nothing
      | otherwise = Test name $ Just $
          "expected" <+> pretty expected <+> "got" <+> pretty term

    pptext :: Doc ann -> Text
    pptext = renderStrict . layoutPretty defaultLayoutOptions


𝓊 :: Int -> CoreUD
𝓊 = Uniχ void

idv :: Integer -> Text -> CoreUD
idv n t = Varχ void $ Name $ Right (n, t)

idn :: Integer -> Text -> Name
idn n t = Name $ Right (n, t)

(⋅) :: CoreUD -> CoreUD -> CoreUD
(⋅) = Appχ void

(⇒) :: [Name] -> CoreUD -> CoreUD
args ⇒ body = foldr (\var body -> Absχ void (OptBind (Just var, Nothing)) body) body args

(→) :: [Name] -> CoreUD -> CoreUD
args → body = foldr (\var body -> Prdχ void (OptBind (Just var, Nothing)) body) body args
