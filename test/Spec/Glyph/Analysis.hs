module Spec.Glyph.Analysis (analysis_spec) where

import TestFramework

import Spec.Glyph.Analysis.NameResolution 
import Spec.Glyph.Analysis.Typecheck 

analysis_spec :: TestGroup
analysis_spec = TestGroup "analysis" $ Left [resolve_spec, type_spec]
