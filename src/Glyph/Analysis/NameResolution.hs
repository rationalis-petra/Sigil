module Glyph.Analysis.NameResolution (resolve) where

import Prelude hiding (lookup)
import Data.Map (Map, lookup, insert, empty)
import Data.Text (Text)

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment hiding (Environment(..)) 

import Glyph.Concrete.Parsed
import Glyph.Concrete.Resolved


{------------------------------- ID GENERATION ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

resolve :: MonadGen m => RawCore -> m ResolvedCore
resolve core = resolve_id' empty core where
  resolve_id' :: MonadGen m => Map Text Integer -> RawCore -> m ResolvedCore
  resolve_id' vars term = case term of 
    Coreχ PUnit -> pure $ Coreχ ()
    Uni χ n -> pure $ Uni χ n
    Var χ name -> case lookup name vars of
      Just n -> pure $ Var χ $ Name $ Right $ (n, name)
      Nothing -> pure $ Var χ $ Name $ Left $ [name]
    Prd χ (OptBind (t, a)) ty -> do
      id <- fresh_id
      let n = (\text -> Name $ Right (id,text)) <$> t
          vars' = maybe vars (\t -> insert t id vars) t
      a' <- mapM (resolve_id' vars') a
      Prd χ (OptBind (n, a')) <$> resolve_id' vars' ty
    Abs χ (OptBind (t, ty)) e -> do
      id <- fresh_id
      let
        n = (\text -> Name $ Right (id,text)) <$> t 
        vars' = maybe vars (\t -> insert t id vars) t
      ty' <- mapM (resolve_id' vars') ty
      Abs χ (OptBind (n, ty')) <$> resolve_id' vars' e
    App χ l r -> App χ <$> (resolve_id' vars l) <*> (resolve_id' vars r)
