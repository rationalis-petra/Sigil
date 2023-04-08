module Spec.Glyph.Abstract (abstract_spec) where

import TestFramework

import Spec.Glyph.Abstract.Syntax 
import Spec.Glyph.Abstract.AlphaEq 

abstract_spec :: TestGroup
abstract_spec = TestGroup "abstract" $ Left
  [ alphaeq_spec
  , syntax_spec
  ]
