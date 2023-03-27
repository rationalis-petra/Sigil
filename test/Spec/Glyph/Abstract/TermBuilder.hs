module Spec.Glyph.Abstract.TermBuilder (
  (→),
  (↦),
  (⋅),
  u,
  un,
  v) where

import Data.Text (Text)
import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment hiding ((↦))

{-------------------------------- TERM BUILDER ---------------------------------}
{- The Term Builder provides an interface letting a programmer build syntax    -}
{- trees more easily for the purposes of testing.                              -}
{-                                                                             -}

void :: a
void = void

(→) :: (Text, Core AnnBind Text χ) -> Core AnnBind Text χ -> Core AnnBind Text χ  
(x, a) → b = Prd void (AnnBind (x, a)) b

(↦) :: [(Text, Core AnnBind Text χ)] -> Core AnnBind Text χ -> Core AnnBind Text χ
args ↦ body = foldr (\(var, ty) body -> Abs void (AnnBind (var, ty)) body) body args

(⋅) :: Core b n χ -> Core b n χ -> Core b n χ  
(⋅) = App void

u :: Core b n χ
u = Uni void 0

un :: Int -> Core b n χ
un = Uni void

v :: Text -> Core b Text χ
v = Var void


  
