module Spec.Sigil.Interpret (interpret_spec) where

import TestFramework

import Spec.Sigil.Interpret.Substitution 
import Spec.Sigil.Interpret.Term 
import Spec.Sigil.Interpret.Unify 

interpret_spec :: TestGroup
interpret_spec = TestGroup "interpret" $ Left
  [ subst_spec
  , term_spec
  , unify_spec
  ]
