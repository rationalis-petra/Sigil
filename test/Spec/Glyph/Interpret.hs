module Spec.Glyph.Interpret (interpret_spec) where

import TestFramework

import Spec.Glyph.Interpret.Substitution 
import Spec.Glyph.Interpret.Term 
import Spec.Glyph.Interpret.Unify 

interpret_spec :: TestGroup
interpret_spec = TestGroup "interpret" $ Left
  [ subst_spec
  , term_spec
  , unify_spec
  ]
