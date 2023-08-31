module Sigil.Compile.ANF (ANFExp(..), ANFVal(..)) where

-- A normal form (with join points)

-- Looks like Haskell et. al extend this with
-- • A Type system
-- • Join points

import Sigil.Abstract.Environment


data ANFExp
  = AEVar Name
  | Let Name ANFVal ANFExp 
  | LetApp Name ANFVal ANFVal ANFExp 

data ANFVal  
  = AVar Name
  | Lam Name ANFExp
  
