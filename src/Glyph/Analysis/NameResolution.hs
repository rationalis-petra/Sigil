module Glyph.Analysis.NameResolution (resolve) where

import Prelude hiding (lookup)
import Data.Map (Map, lookup, insert, empty)
import Data.Text (Text)

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment hiding (Environment(..)) 


{------------------------------- ID GENERATION ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


resolve :: MonadGen m => Core OptBind Text χ -> m (Core OptBind Name χ)
resolve core = resolve_id' empty core where
  resolve_id' :: MonadGen m => Map Text Integer -> Core OptBind Text χ -> m (Core OptBind Name χ)
  resolve_id' vars term = case term of 
    Coreχ χ -> pure $ Coreχ χ
    Uni χ n -> pure $ Uni χ n
    Var χ name -> case lookup name vars of
      Just n -> pure $ Var χ $ Name $ Right $ (n, name)
      Nothing -> pure $ Var χ $ Name $ Left $ [name]
    Prd χ (OptBind bind) ty -> do
      id <- fresh_id
      case bind of
        Left var -> 
          let var' = Name $ Right (id, var) in
          Prd χ (OptBind $ Left var') <$> (resolve_id' (insert var id vars) ty)
        Right (var, a) -> do
          let var' = Name $ Right (id, var)
          a' <- resolve_id' (insert var id vars) a
          Prd χ (OptBind $ Right (var', a')) <$> (resolve_id' (insert var id vars) ty)
    Abs χ (OptBind bind) e -> do
      id <- fresh_id
      case bind of
        Left var -> 
          let var' = Name $ Right (id, var) in
          Abs χ (OptBind $ Left var') <$> (resolve_id' (insert var id vars) e)
        Right (var, ty) -> do
          let var' = Name $ Right (id, var)
          ty' <- resolve_id' (insert var id vars) ty
          Abs χ (OptBind $ Right (var', ty')) <$> (resolve_id' (insert var id vars) e)
    App χ l r -> App χ <$> (resolve_id' vars l) <*> (resolve_id' vars r)
