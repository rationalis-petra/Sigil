module Spec.Glyph.Parse (parse_spec) where

import Data.Text (Text)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Vector as Vec

import Prettyprinter
import Topograph

import TestFramework
import Glyph.Parse
import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment

nr :: Range
nr = ([], -1, -1)

var :: Text -> Core b Text Parsed  
var = Var nr

-- ilit :: Integer -> Core Parsed
-- ilit i = Coreχ (nr, PLInteger i) 

-- dlit :: Double -> Core Parsed
-- dlit d = Coreχ (nr, PLReal d)


ops :: Map PrecedenceNode (Set PrecedenceNode)
ops = Map.fromList
  [ (node_and,   Set.singleton node_eq)
  , (node_eq,    Set.fromList  [node_arith, node_fact])
  , (node_arith, Set.singleton node_close)
  , (node_fact,  Set.singleton node_close)
  , (node_if,    Set.singleton node_close)
  , (node_close, Set.empty) ]

  where 
    node_and   = Set.singleton and_op
    node_eq    = Set.singleton eq_op
    node_arith = Set.fromList [add_op, sub_op]
    node_fact  = Set.fromList [fact_op]
    node_if    = Set.singleton if_op
    node_close = Set.fromList [paren_op, true, false]
    
    true     = Operator Closed $ Vec.singleton "true"
    false    = Operator Closed $ Vec.singleton "false"
    and_op   = Operator (Infix RightAssociative) $ Vec.fromList ["&"]
    eq_op    = Operator (Infix NonAssociative)   $ Vec.fromList ["="]
    add_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["+"]
    sub_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["-"]
    fact_op  = Operator Postfix $ Vec.fromList ["!"]
    if_op    = Operator Prefix $ Vec.fromList ["if", "then", "else"]
    paren_op = Operator Closed $ Vec.fromList ["(", ")"]
    --mis_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["∧"]

-- printing out gives

{--

[ fromList [ Operator {_fixity = Infix RightAssociative, _name_parts = ["&"]} ]
, fromList [ Operator {_fixity = Infix NonAssociative  , _name_parts = ["="]} ]
, fromList [ Operator {_fixity = Infix LeftAssociative , _name_parts = ["+"]}
           , Operator {_fixity = Infix LeftAssociative , _name_parts = ["-"]} ]
, fromList [ Operator {_fixity = Postfix, _name_parts = ["!"]}]
, fromList [ Operator {_fixity = Prefix, _name_parts = ["if","then","else"]} ]
, fromList [ Operator {_fixity = Closed, _name_parts = ["(",")"]}
           , Operator {_fixity = Closed, _name_parts = ["false"]}
           , Operator {_fixity = Closed, _name_parts = ["true"]}]]

--}  

  

parse_spec :: TestGroup
parse_spec =
  case runG ops go of
    Left _ -> TestGroup "parsing" $ Right
      [Test "parsing" $ Just ("parsing test-suite failed to run as there was a cycle in the precedence graph")]
    Right tests -> tests
  where
    go :: PrecedenceGraph i -> TestGroup
    go graph = TestGroup "parsing" $ Left
      [ parse_mixfix graph
      , parse_expr graph ]


-- parsing of mixfix operations 
parse_mixfix :: PrecedenceGraph i -> TestGroup
parse_mixfix graph =
  -- tests to add
  -- Backtracking / garden path
    -- operators which have shared name parts, ex. if_then_ and if_then_else_
    -- names with similar beginnings, e.g. 'in' and 'inner' 
  -- test for features as they are added. 
  
  TestGroup "parse-mixfix" $ Right
    -- Closed Operations
    [ mixfix_test "lit-true" "true" (var "true")
    , mixfix_test "lit-false" "false" (var "false")
    , mixfix_test "parens-lit" "( true )" (App nr (var "(_)") (var "true"))

    -- TODO: these tests fail. Speculation: it's related to the fact that they
    -- have successor nodes which are infix operations!
    , mixfix_test "bin-of-lit1" "true = false" (App nr (App nr (var "_=_") (var "true" )) (var "false"))
    
    -- Right Associative Operations 
    -- , mixfix_test "true & false" (App nr (App nr (var "_&_") (var "true" )) (var "false"))
    -- , mixfix_test graph "true ∧ false" (App nr (App nr (var "_∧_") (var "true" )) (App nr (var "false") (var "true"))) 

    -- Left Associative Operations 
    , mixfix_test "bin-of-lit2" "true + false" (App nr (App nr (var "_+_") (var "true" )) (var "false"))
    , mixfix_test "bin-precedence" "true + false - false"
        (App nr (App nr (var "_-_")
                 (App nr (App nr (var "_+_") (var "true" )) (var "false")))
                (var "false"))

    -- , mixfix_test graph "if true then false else false"
    --     (App nr (App nr (App nr (var "if_then_else_") (var "true")) (var "false")) (var "false"))
    ]

  where
    mixfix_test :: Text -> Text -> Core OptBind Text Parsed -> Test
    mixfix_test name text out =  
      case runParser (mixfix graph) "test" text of  
        Right val ->
          if val == out then
            Test name Nothing
          else
            Test name $ Just $ "values inequal: " <> pretty val <> " and " <> pretty out
        Left msg -> Test name $ Just $ pretty msg

parse_expr :: PrecedenceGraph i -> TestGroup
parse_expr graph =
  TestGroup "parse-expr" $ Right
    [ expr_test "univar-lambda" "λ [x] true" (abs [("x")] (var "true"))
    , expr_test "bivar-lambda" "λ [x y] false" (abs ["x", "y"] (var "false"))
    ]

  where
    expr_test :: Text -> Text -> Core OptBind Text Parsed -> Test
    expr_test name text out =  
      case runParser (core graph) "test" text of  
        Right val ->
          if val == out then
            Test name Nothing
          else
            Test name $ Just $ "values inequal: " <> pretty val <> " and " <> pretty out
        Left msg -> Test name $ Just $ pretty msg


    abs :: [Text] -> Core OptBind Text Parsed -> Core OptBind Text Parsed
    abs = flip $ foldr (\var body -> Abs nr (OptBind $ Left var) body)
