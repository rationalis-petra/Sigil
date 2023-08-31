module Spec.Sigil.Abstract (abstract_spec) where

import TestFramework

import Spec.Sigil.Abstract.Syntax 
import Spec.Sigil.Abstract.AlphaEq 

abstract_spec :: TestGroup
abstract_spec = TestGroup "abstract" $ Left
  [ alphaeq_spec
  , syntax_spec
  ]
