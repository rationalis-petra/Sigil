module Spec.Sigil.Parse (parse_spec) where

import Prelude hiding (abs, pi, mod)
import Data.Bifunctor
import Data.Text (Text)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Vector as Vec

import Prettyprinter
import Prettyprinter.Render.Sigil

import TestFramework
import Sigil.Parse
import Sigil.Parse.Mixfix
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Abstract.AlphaEq
import Sigil.Concrete.Parsed


expr_ops :: Map Text PrecedenceNode
expr_ops = Map.fromList
  [("ctrl",  PrecedenceNode node_ctrl  (Set.fromList ["ppd"]))

  , ("eq",    PrecedenceNode node_eq    (Set.fromList ["sum"]))
  , ("sum",   PrecedenceNode node_sum   (Set.fromList ["prod"]))
  , ("prod",  PrecedenceNode node_prod  (Set.fromList ["ppd"]))
  , ("ppd",   PrecedenceNode node_ppd   (Set.fromList ["tight"]))
  , ("tight", PrecedenceNode node_tight (Set.fromList ["close"]))
  , ("close", PrecedenceNode node_close (Set.empty))
  ]

  where 
    node_eq    = Set.fromList [eq_op, neq_op]
    node_sum   = Set.fromList [add_op, sub_op, or_op]
    node_prod  = Set.fromList [times_op, dot_op, and_op]
    node_ppd   = Set.fromList [fact_op, f_op, g_op]
    node_tight = Set.fromList [pm_op]
    node_ctrl  = Set.fromList [if_op]
    node_close = Set.fromList [true, false]
    
    if_op    = Operator Prefix $ Vec.fromList ["if", "then", "else"]
    eq_op    = Operator (Infix NonAssociative)   $ Vec.fromList ["="]
    neq_op   = Operator (Infix NonAssociative)   $ Vec.fromList ["≠"]

    or_op    = Operator (Infix RightAssociative) $ Vec.fromList ["∨"]
    add_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["+"]
    sub_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["-"]

    and_op   = Operator (Infix RightAssociative) $ Vec.fromList ["∧"]
    dot_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["⋅"]
    times_op = Operator (Infix LeftAssociative)  $ Vec.fromList ["×"]

    fact_op  = Operator Postfix $ Vec.fromList ["!"]
    f_op     = Operator Prefix $ Vec.fromList ["f"]
    g_op     = Operator Prefix $ Vec.fromList ["g"]

    pm_op    = Operator Prefix $ Vec.fromList ["±"]
   
    true     = Operator Closed $ Vec.singleton "true"
    false    = Operator Closed $ Vec.singleton "false"


precs :: Precedences
precs = Precedences
  { _prec_nodes=expr_ops
  , _default_infix="sum"
  , _default_prefix="ppd"
  , _default_postfix="ppd"
  , _default_closed="close"
  }

parse_spec :: TestGroup
parse_spec = TestGroup "parsing" $ Left
  [ parse_lit precs
  , parse_mixfix precs
  , parse_expr precs
  , parse_entry precs
  , parse_mod (const precs)
  ]
      
-- parsing of mixfix operations 
parse_mixfix :: Precedences -> TestGroup
parse_mixfix precs = TestGroup "mixfix" $ Right
    -- Simple tests
    [ mixfix_test "lit-true" "true" (var "true")
    , mixfix_test "lit-false" "false" (var "false")
    --, mixfix_test "simple-closed" "( true )" (var "(_)" ⋅ var "true")
    , mixfix_test "simple-postfix" "true !" (var "_!" ⋅ var "true" )
    , mixfix_test "simple-prefix" "f true" (var "f_" ⋅ var "true")
    , mixfix_test "simple-non-assoc" "true = false" (var "_=_" ⋅ var "true" ⋅ var "false")
    , mixfix_test "simple-left-assoc" "true + false" (var "_+_" ⋅ var "true"  ⋅ var "false")
    , mixfix_test "simple-right-assoc" "true ∧ false" (var "_∧_" ⋅ var "true"  ⋅ var "false")
    , mixfix_test "close_app" "true true" (var "true" ⋅ var "true")

    --, mixfix_test "simple-close-prefix" "true true" (var "true" ⋅ var "true")
    --, mixfix_test "mutli-prefix" "func true true" (var "func_" ⋅ var "true" ⋅ var "true")

    -- Multiple name parts tests
    , mixfix_test "simple-multiname-prefix" "if true then false else true"
           (var "if_then_else_" ⋅ var "true" ⋅ var "false" ⋅ var "true")
    -- , mixfix_test "simple-multiname-postfix"
    -- , mixfix_test "simple-multiname-nonassoc"
    -- , mixfix_test "simple-multiname-left-assoc"
    -- , mixfix_test "simple-multiname-right-assoc" 

    -- Associativity Tests
    , mixfix_test "multiple-right-assoc" "true ∧ false ∧ false"
      (var "_∧_"
       ⋅ var "true"
       ⋅ (var "_∧_" ⋅ var "false" ⋅ var "false"))

    , mixfix_test "multiple-left-assoc" "true + false - false"
      (var "_-_"
        ⋅ (var "_+_" ⋅ var "true"  ⋅ var "false")
        ⋅ var "false")

    -- Combining Operations (precedence tests)
    --, mixfix_test "paren-binop" "(true + false)" (var "(_)" ⋅ (var "_+_" ⋅ var "true"  ⋅ var "false" ))

    , mixfix_test "binop-precedence" "true + false ⋅ false" (var "_+_" ⋅ var "true"  ⋅ (var "_⋅_" ⋅ var "false" ⋅ var "false"))
    ]

  where
    mixfix_test :: Text -> Text -> ParsedCore -> Test
    mixfix_test name text out =  
      case runParser (mixfix (fail "no core") (fail "no atom") precs) name text of  
        Right val ->
          if αeq val out then
            Test name Nothing
          else
            Test name $ Just $
              "got:" <+> annotate (fg_colour (dull white)) (pretty val) <+>
              "expected:" <+> annotate (fg_colour (dull white)) (pretty out)
        Left msg -> Test name $ Just msg

parse_lit :: Precedences -> TestGroup
parse_lit graph =
  TestGroup "literal" $ Right
    [ lit_test "universe-0"   "𝕌"   (𝓊 0)
    , lit_test "universe-0v2" "𝕌₀"  (𝓊 0)
    , lit_test "universe-1"   "𝕌₁"  (𝓊 1)
    , lit_test "universe-10"  "𝕌₁₀" (𝓊 10)
    , lit_test "universe-23"  "𝕌₂₃" (𝓊 23)
    ]

  where
    lit_test :: Text -> Text -> ParsedCore -> Test
    lit_test name text out =  
      case runParser (core graph) name text of  
        Right val ->
          if αeq val out then
            Test name Nothing
          else
            Test name $ Just $ "got:" <+> "(" <> pretty val <>")" <+> "expected" <+> "(" <> pretty out <> ")"
        Left msg -> Test name $ Just msg

parse_expr :: Precedences -> TestGroup
parse_expr graph =
  TestGroup "expression" $ Right
    [ expr_test "universe-in-expr" "𝕌 + 𝕌" (var "_+_" ⋅ 𝓊 0 ⋅ 𝓊 0)
    , expr_test "univar-lamb" "λ x → true" (abs ["x"] (var "true"))
    , expr_test "bivar-lamb" "λ x y → false" (abs ["x", "y"] (var "false"))

    , expr_test "closed-lamb"
      "λ x → x"
      (abs ["x"] (var "x"))
    , expr_test "infix-lamb"
      "λ _x_ → true x true"
      (abs ["_x_"] (var "_x_" ⋅ var "true" ⋅ var "true"))
    , expr_test "infix-closed_lamb"
      "λ _x_ th fo → th x fo"
      (abs ["_x_", "th", "fo"] (var "_x_" ⋅ var "th" ⋅ var "fo"))
    , expr_test "prefix-lamb"
      "λ x_ → x true"
      (abs ["x_"] (var "x_" ⋅ var "true"))
    , expr_test "postfix-lamb"
      "λ _x → true x"
      (abs ["_x"] (var "_x" ⋅ var "true"))

    , expr_test "uni-uni-app"
      "𝕌 𝕌"
      (𝓊 0 ⋅ 𝓊 0)
    -- slow
    -- , expr_test "lamb-in-expr"
    --   "(λ [x_] x true) + (λ [x_] x true) "
    --   (var "_+_" ⋅ (abs ["x_"] (var "x_" ⋅ var "true")) ⋅ (abs ["x_"] (var "x_" ⋅ var "true")))
    -- , expr_test "uni-uni-paren-app"
    --   "(𝕌 𝕌)"
    --   (𝓊 0⋅ 𝓊 0)
    -- , expr_test "lam-var-app"
    --   "(λ [x_] x true) true"
    --   ((abs ["x_"] (var "x_" ⋅ var "true")) ⋅ var "true")
    -- , expr_test "lam-uni-app"
    --   "(λ [x_] x true) 𝕌"
    --   ((abs ["x_"] (var "x_" ⋅ var "true")) ⋅ 𝓊 0)
    -- , expr_test "lam-lam-app"
    --   "(λ [x_] x true) (λ [x_] x true)"
    --   ((abs ["x_"] (var "x_" ⋅ var "true")) ⋅ (abs ["x_"] (var "x_" ⋅ var "true")))

    -- Lambda: Annotations, multiple arguments etc.
    , expr_test "lam-ann"
      "λ (A ⮜ 𝕌) → A"
      (lam [("A", 𝓊 0)] (var "A"))
    , expr_test "lam-many"
      "λ (A ⮜ 𝕌) (B ⮜ 𝕌) → A"
      (lam [("A", 𝓊 0), ("B", 𝓊 0)] (var "A"))
    , expr_test "lam-dep"
      "λ (A ⮜ 𝕌) (x ⮜ A) → x"
      (lam [("A", 𝓊 0), ("x", var "A")] (var "x"))

    -- Product: Annotations, multiple arguments etc.
    , expr_test "prd-ann"
      "(A ⮜ 𝕌) → A"
      (pi [("A", 𝓊 0)] (var "A"))
    , expr_test "prd-noann"
      "𝕌 → 𝕌"
      ([𝓊 0] → 𝓊 0)
    ]
  where
    expr_test :: Text -> Text -> ParsedCore -> Test
    expr_test name text out =  
      case runParser (core graph) name text of  
        Right val ->
          if αeq val out then
            Test name Nothing
          else
            Test name $ Just $ "got:" <+> "(" <> pretty val <>")" <+> "expected" <+> "(" <> pretty out <> ")"
        Left msg -> Test name $ Just msg


parse_entry :: Precedences -> TestGroup
parse_entry precs = 
  TestGroup "definition" $ Right
    [ entry_test "literal"
      "x ≜ true"
      (sentry "x" (var "true"))
    , entry_test "recursive"
      "x ≜ x"
      (sentry "x" (var "x"))
    , entry_test "parameter"
      "id y ≜ y"
      (sentry "id" (abs ["y"] (var "y")))
    , entry_test "infix-param"
      "twice _*_ y ≜ y * y"
      (sentry "twice" (abs ["_*_", "y"] (var "_*_" ⋅ var "y" ⋅ var "y")))
    , entry_test "posfix-param"
      "post-app x _~ ≜ x ~"
      (sentry "post-app" (abs ["x", "_~"] (var "_~" ⋅ var "x")))
    ]
  where
    entry_test :: Text -> Text -> Entry OptBind Text Parsed -> Test
    entry_test name text out =  
      case runParser (entry precs) name text of  
        Right val ->
          if αeq val out then
            Test name Nothing
          else
            Test name $ Just $ "got: " <> pretty val <+> "expected" <+> pretty out
        Left msg -> Test name $ Just msg

parse_mod :: ([ImportDef] -> Precedences) -> TestGroup
parse_mod env = 
  TestGroup "module" $ Right
    [ mod_test "empty"
      "module empty"
      (modul ["empty"] [] [] []),

      mod_test "single-def"
      "module single-def \n\
      \x ≜ true"
      (modul ["single-def"] [] [] [sentry "x" (var "true")]),

      mod_test "multi-def"
      "module multi-def \n\
      \x ≜ true\n\
      \y ≜ false"
      (modul ["multi-def"] [] [] [sentry "x" (var "true"), sentry "y" (var "false")]),

      mod_test "complex-modul"
      "module complex-modul \n\
      \fn ≜ λ (A ⮜ 𝕌₁) (x ⮜ A) → A\n\
      \val ≜ fn 𝕌"
      (modul ["complex-modul"] [] []
       [ sentry "fn" (lam [("A", 𝓊 1), ("x", var "A")] (var "A"))
       , sentry "val" (var "fn" ⋅ 𝓊 0)
       ])
    ]
  where
    mod_test :: Text -> Text -> ParsedModule -> Test
    mod_test name text out =  
      case runParser (mod (\_ i -> pure (env i))) name text of  
        Right val ->
          if αeq val out then
            Test name Nothing
          else
            Test name $ Just $ vsep ["got:", pretty val, "expected:", pretty out]
        Left msg -> Test name $ Just msg

𝓊 :: Int -> ParsedCore  
𝓊 = Uniχ mempty

var :: Text -> ParsedCore  
var = Varχ mempty

abs :: [Text] -> ParsedCore -> ParsedCore
abs = flip $ foldr (\var body -> Absχ mempty (OptBind (Just var, Nothing)) body)

lam :: [(Text, ParsedCore)] -> ParsedCore -> ParsedCore
lam = flip (foldr (Absχ mempty)) . fmap (OptBind . bimap Just Just)

pi :: [(Text, ParsedCore)] -> ParsedCore -> ParsedCore
pi = flip (foldr (Prdχ mempty)) . fmap (OptBind . bimap Just Just)

(→) :: [ParsedCore] -> ParsedCore -> ParsedCore
(→) = flip (foldr (Prdχ mempty)) . fmap (\t -> OptBind (Nothing, Just t))

(⋅) :: ParsedCore -> ParsedCore -> ParsedCore
(⋅) = Appχ mempty

sentry :: Text -> ParsedCore -> ParsedEntry
sentry name val = Singleχ mempty (OptBind (Just name, Nothing)) val

modul :: [Text] -> [ImportDef] -> [ExportDef] -> [ParsedEntry] -> ParsedModule
modul = Module 
