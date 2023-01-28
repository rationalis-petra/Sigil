
import Control.Monad (when)

import Spec.Glyph.Syntax.Core
import Spec.Glyph.Parse
import Spec.Glyph.NameResolution


main :: IO ()
main = do
  putStrLn ""
  when parse_p parse_spec
  when core_p core_spec
  when resolve_p resolve_spec
  putStrLn "Testing Complete"

  where
    parse_p = True
    core_p = True
    resolve_p = True
