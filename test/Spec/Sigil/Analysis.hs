module Spec.Sigil.Analysis (analysis_spec) where

import TestFramework

import Spec.Sigil.Analysis.NameResolution 
import Spec.Sigil.Analysis.Typecheck 

analysis_spec :: TestGroup
analysis_spec = TestGroup "analysis" $ Left [resolve_spec, type_spec]
