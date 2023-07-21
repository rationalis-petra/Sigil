module Spec.Glint.Parse (gl_parse_spec) where

--import Data.Text (Text)

--import Prettyprinter
--import Prettyprinter.Render.Glyph

import TestFramework

--import Glint.Syntax
--import Glint.Parse


gl_parse_spec :: TestGroup
gl_parse_spec = TestGroup "gl_parsing" $ Right
    [ --node_test "empty-block" "[m|]" (Node "m" [] [] [])
    ]
  -- where
  --   node_test :: Text -> Text -> GlnRaw -> Test
  --   node_test name text out =
  --     case runParser glint name text of  
  --       Right val ->
  --         if val == out then
  --           Test name Nothing
  --         else
  --           Test name $ Just $
  --             "got:" <+> annotate (fg_colour (dull white)) (pretty val) <+>
  --             "expected:" <+> annotate (fg_colour (dull white)) (pretty out)
  --       Left msg -> Test name $ Just msg
