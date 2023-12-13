module Sigil.Analysis.FormulaCheck
  ( check_formula ) where

import Control.Monad.Except (MonadError, throwError)

import Prettyprinter

import Sigil.Abstract.Names
import Sigil.Abstract.Unify
import Sigil.Abstract.Environment
import Sigil.Analysis.Typecheck
import Sigil.Concrete.Resolved
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Internal


check_formula :: (MonadGen m, MonadError err m, Environment Name e)
  => CheckInterp m err e InternalCore -> e (Maybe InternalCore,InternalCore)
  -> Formula Name ResolvedCore -> m (Formula Name InternalCore)
check_formula interp@(CheckInterp {..}) env formula = case formula of 
  Conj scons -> Conj <$> mapM (check_scons interp env) scons
  And l r -> And <$> check_formula interp env l <*> check_formula interp env r
  Bind q n ty f -> do
    (ty', kind) <- infer interp env ty
    ty_norm <- normalize (lift_err . flip NormErr mempty) env kind ty'
    let env' = insert n (Nothing, ty_norm) env
    Bind q n ty_norm <$> check_formula interp env' f 


check_scons :: (MonadGen m, MonadError err m, Environment Name e)
  => CheckInterp m err e InternalCore -> e (Maybe InternalCore,InternalCore)
  -> SingleConstraint ResolvedCore -> m (SingleConstraint InternalCore)
check_scons interp@(CheckInterp {..}) env cons = case cons of
  (l :≗: r) -> do
    (l', lty) <- infer interp env l
    (r', rty) <- infer interp env r
    (_, kind) <- infer interp env lty
    check_eq mempty interp env kind lty rty
    l_norm <- normalize (lift_err . flip NormErr mempty) env lty l'
    r_norm <- normalize (lift_err . flip NormErr mempty) env rty r'
    pure $ (l_norm :≗: r_norm)
  (val :∈: ty) -> do
    (ty', kind) <- infer interp env ty
    ty_norm <- normalize (lift_err . flip NormErr mempty) env kind ty'
    val' <- check interp env val ty_norm
    val_norm <- normalize (lift_err . flip NormErr mempty) env ty_norm val'
    pure $ (val_norm :≗: ty_norm)


check_eq :: (MonadError err m, Pretty a) => Range -> (CheckInterp m err e a) -> e (Maybe a, a) -> a -> a -> a -> m ()
check_eq range (CheckInterp {..}) env ty l r
 = 
  αβη_eq (lift_err . flip NormErr range) env ty l r >>= \case
    True -> pure ()
    False -> throwError $ lift_err $ PrettyErr ("not-equal:" <+> pretty l <+> "and" <+> pretty r) range
