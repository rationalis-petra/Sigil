module Spec.Glyph.Parse (parse_spec) where

import Prelude hiding (abs)
import Data.Text (Text)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Vector as Vec

import Prettyprinter
import Prettyprinter.Render.Glyph
import Topograph

import TestFramework
import Glyph.Parse
import Glyph.Parse.Mixfix
import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment
import Glyph.Abstract.AlphaEq
import Glyph.Concrete.Parsed


ops :: [Map PrecedenceNode (Set PrecedenceNode)]
ops =
  [ Map.fromList
    [ (node_and,   Set.singleton node_eq)
    , (node_eq,    Set.fromList  [node_arith, node_fact])
    , (node_arith, Set.singleton node_close)
    , (node_fact,  Set.singleton node_close)
    , (node_if,    Set.singleton node_close)
    , (node_close, Set.empty)
    ]
  , Map.fromList
    [ (node_and,   Set.singleton node_eq)
    , (node_eq,    Set.fromList  [node_arith, node_fact])
    , (node_arith, Set.empty)
    , (node_fact,  Set.empty)
    , (node_if,    Set.empty)
    ]
  ]

  where 
    node_and   = Set.singleton and_op
    node_eq    = Set.singleton eq_op
    node_arith = Set.fromList [add_op, sub_op]
    node_fact  = Set.fromList [fact_op, func_op]
    node_if    = Set.singleton if_op
    node_close = Set.fromList [paren_op, true, false]
    
    true     = Operator Closed $ Vec.singleton "true"
    false    = Operator Closed $ Vec.singleton "false"
    and_op   = Operator (Infix RightAssociative) $ Vec.fromList ["∧"]
    eq_op    = Operator (Infix NonAssociative)   $ Vec.fromList ["="]
    add_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["+"]
    sub_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["-"]
    fact_op  = Operator Postfix $ Vec.fromList ["!"]
    func_op  = Operator Prefix $ Vec.fromList ["func"]
    if_op    = Operator Prefix $ Vec.fromList ["if", "then", "else"]
    paren_op = Operator Closed $ Vec.fromList ["(", ")"]


precs :: Precedences
precs = Precedences (ops !! 1) $ Set.fromList
  [ Operator Closed $ Vec.singleton "true"
  , Operator Closed $ Vec.singleton "false"
  , Operator Closed $ Vec.fromList ["(", ")"]
  ]

parse_spec :: TestGroup
parse_spec = TestGroup "parsing" $ Left
  [ parse_mixfix (ops !! 0)
  , parse_expr precs
  , parse_def precs
  ]
      
parse_mixfix :: Map PrecedenceNode (Set PrecedenceNode) -> TestGroup
parse_mixfix graph = TestGroup "mixfix" $ Right $
  case runG graph (parse_mixfix' . closure) of
    Left _ -> 
      [ Test "group-failed" $ Just ("parsing test-suite failed to run as there was a cycle in the precedence graph") ]
    Right tests -> tests

-- parsing of mixfix operations 
parse_mixfix' :: PrecedenceGraph i -> [Test]
parse_mixfix' graph =
    -- Simple tests
    [ mixfix_test "lit-true" "true" (var "true")
    , mixfix_test "lit-false" "false" (var "false")
    , mixfix_test "simple-closed" "( true )" (var "(_)" ⋅ var "true")
    , mixfix_test "simple-postfix" "true !" (var "_!" ⋅ var "true" )
    , mixfix_test "simple-prefix" "func true" (var "func_" ⋅ var "true")
    , mixfix_test "simple-non-assoc" "true = false" (var "_=_" ⋅ var "true" ⋅ var "false")
    , mixfix_test "simple-left-assoc" "true + false" (var "_+_" ⋅ var "true"  ⋅ var "false")
    , mixfix_test "simple-right-assoc" "true ∧ false" (var "_∧_" ⋅ var "true"  ⋅ var "false")

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
    , mixfix_test "paren-binop" "(true + false)" (var "(_)" ⋅ (var "_+_" ⋅ var "true"  ⋅ var "false" ))
    ]

  where
    mixfix_test :: Text -> Text -> RawCore -> Test
    mixfix_test name text out =  
      case runParser (mixfix (fail "no core") graph) name text of  
        Right val ->
          if αeq val out then
            Test name Nothing
          else
            Test name $ Just $
              "got:" <+> annotate (fg_colour (dull white)) (pretty val) <+>
              "expected:" <+> annotate (fg_colour (dull white)) (pretty out)
        Left msg -> Test name $ Just $ pretty msg

parse_expr :: Precedences -> TestGroup
parse_expr graph =
  TestGroup "expression" $ Right
    [ expr_test "univar-lambda" "λ [x] true" (abs [("x")] (var "true"))
    , expr_test "bivar-lambda" "λ [x y] false" (abs ["x", "y"] (var "false"))

    , expr_test "simple-close-prefix" "true true" (var "true" ⋅ var "true")

    , expr_test "closed-lambda"
      "λ [x] x"
      (abs [("x")] (var "x"))
    , expr_test "infix-lambda"
      "λ [_x_] true x true"
      (abs ["_x_"] (var "_x_" ⋅ var "true" ⋅ var "true"))
    , expr_test "infix-closed_lambda"
      "λ [_x_ th fo] th x fo"
      (abs ["_x_", "th", "fo"] (var "_x_" ⋅ var "th" ⋅ var "fo"))
    , expr_test "prefix-lambda"
      "λ [x_] x true"
      (abs ["x_"] (var "x_" ⋅ var "true"))
    , expr_test "postfix-lambda"
      "λ [_x] true x"
      (abs ["_x"] (var "_x" ⋅ var "true"))

    , expr_test "lambda-app"
      "(λ [x_] x true) true"
      ((abs ["x_"] (var "x_" ⋅ var "true")) ⋅ var "true")
    , expr_test "lambda-app"
      "(λ [x_] x true) (λ [x_] x true)"
      ((abs ["x_"] (var "x_" ⋅ var "true")) ⋅ (abs ["x_"] (var "x_" ⋅ var "true")))
    ]
  where
    expr_test :: Text -> Text -> Core OptBind Text Parsed -> Test
    expr_test name text out =  
      case runParser (core graph) name text of  
        Right val ->
          if αeq val out then
            Test name Nothing
          else
            Test name $ Just $ "got: " <> pretty val <+> "expected" <+> pretty out
        Left msg -> Test name $ Just $ pretty msg


parse_def :: Precedences -> TestGroup
parse_def precs = 
  TestGroup "definition" $ Right
    [ def_test "literal"
      "x ≜ true"
      (vdef "x" (var "true"))
    , def_test "recursive"
      "x ≜ x"
      (vdef "x" (var "x"))
    , def_test "parameter"
      "id y ≜ y"
      (vdef "id" (abs ["y"] (var "y")))
    , def_test "infix-param"
      "twice _*_ y ≜ y * y"
      (vdef "twice" (abs ["_*_", "y"] (var "_*_" ⋅ var "y" ⋅ var "y")))
    , def_test "posfix-param"
      "post-app x _~ ≜ x ~"
      (vdef "post-app" (abs ["x", "_~"] (var "_~" ⋅ var "x")))
    ]
  where
    def_test :: Text -> Text -> Definition OptBind Text Parsed -> Test
    def_test name text out =  
      case runParser (def precs) name text of  
        Right val ->
          if αeq val out then
            Test name Nothing
          else
            Test name $ Just $ "got: " <> pretty val <+> "expected" <+> pretty out
        Left msg -> Test name $ Just $ pretty msg

(⋅) :: Core OptBind Text Parsed -> Core OptBind Text Parsed -> Core OptBind Text Parsed
(⋅) = App mempty

var :: Text -> Core b Text Parsed  
var = Var mempty

abs :: [Text] -> Core OptBind Text Parsed -> Core OptBind Text Parsed
abs = flip $ foldr (\var body -> Abs mempty (OptBind $ Left var) body)

vdef :: Text -> Core OptBind Text Parsed -> Definition OptBind Text Parsed
vdef name val = Mutual [(OptBind $ Left name, val)]
