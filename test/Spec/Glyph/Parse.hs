module Spec.Glyph.Parse (parse_spec) where

import Control.Lens
import Data.Text (Text, unpack)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Vector as Vec

import Prettyprinter
import Prettyprinter.Render.Text
import Topograph

import Glyph.Parse
import Glyph.Core

nr :: Range
nr = ([], -1, -1)

var :: Text -> Core Text Parsed  
var = Var nr

render :: Core Text Parsed -> Text
render = renderStrict . layoutPretty defaultLayoutOptions . pretty

-- ilit :: Integer -> Core Parsed
-- ilit i = Coreχ (nr, PLInteger i) 

-- dlit :: Double -> Core Parsed
-- dlit d = Coreχ (nr, PLReal d)


ops :: Map Precedence (Set Precedence)
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

  

parse_spec :: IO ()
parse_spec = do
  case runG ops go of
    Left _ -> putStrLn "cycle in ops graph"
    Right mnd -> mnd
  where
    go :: PrecedenceGraph i -> IO ()
    go graph = do
      parse_mixfix graph
      parse_core graph
      putStrLn "parsing suite passed"


-- parsing of mixfix operations 
parse_mixfix :: PrecedenceGraph i -> IO ()
parse_mixfix graph = do
  -- tests to add
  -- Backtracking / garden path
    -- operators which have shared name parts, ex. if_then_ and if_then_else_
    -- names with similar beginnings, e.g. 'in' and 'inner' 
  -- test for features as they are added. 
  
  runtests $
    -- Closed Operations
    [ mixfix_test "true" (var "true")
    , mixfix_test "false" (var "false")
    , mixfix_test "( true )" (App nr (var "(_)") (var "true"))

    -- TODO: these tests fail. Speculation: it's related to the fact that they
    -- have successor nodes which are infix operations!
    --, mixfix_test "true = false" (App nr (App nr (var "_=_") (var "true" )) (var "false"))
    
    -- Right Associative Operations 
    --, mixfix_test "true & false" (App nr (App nr (var "_&_") (var "true" )) (var "false"))
    -- , mixfix_test graph "true ∧ false" (App nr (App nr (var "_∧_") (var "true" )) (App nr (var "false") (var "true"))) 

    -- Left Associative Operations 
    , mixfix_test "true + false" (App nr (App nr (var "_+_") (var "true" )) (var "false"))
    , mixfix_test "true + false - false"
        (App nr (App nr (var "_-_")
                 (App nr (App nr (var "_+_") (var "true" )) (var "false")))
                (var "false"))

    -- , mixfix_test graph "if true then false else false"
    --     (App nr (App nr (App nr (var "if_then_else_") (var "true")) (var "false")) (var "false"))
    ]

  where
    runtests = mapM_ $ mapM_ (putStrLn . unpack . mappend "error: ")

    mixfix_test :: Text -> Core Text Parsed -> Maybe Text
    mixfix_test text out =  
      case runParser (mixfix graph^.expr) "test" text of  
        Right val ->
          if val == out then
            Nothing
          else
            Just $ "values inequal: " <> render val <> " and " <> render out
        Left msg -> Just msg

parse_core :: PrecedenceGraph i -> IO ()
parse_core graph = do
  
  runtests $
    [ core_test "λ [x] true" (abs [("x")] (var "true"))
    , core_test "λ [x y] false" (abs ["x", "y"] (var "false"))
    ]

  where
    runtests = mapM_ $ mapM_ (putStrLn . unpack . mappend "error: ")

    core_test :: Text -> Core Text Parsed -> Maybe Text
    core_test text out =  
      case runParser (core graph) "test" text of  
        Right val ->
          if val == out then
            Nothing
          else
            Just $ "values inequal: " <> render val <> " and " <> render out
        Left msg -> Just msg


    abs :: [Text] -> Core Text Parsed -> Core Text Parsed
    abs = flip $ foldr (\var body -> Abs nr var body)
