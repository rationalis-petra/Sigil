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

resolve :: MonadGen m => ParsedCore -> m ResolvedCore
resolve core = resolve_id' empty core where
  resolve_id' :: MonadGen m => Map Text Integer -> ParsedCore -> m ResolvedCore
  resolve_id' vars term = case term of 
    Core -> pure $ Coreχ ()
    Uni rn n -> pure $ Uniχ rn n
    Var rn name -> case lookup name vars of
      Just n -> pure $ Varχ rn $ Name $ Right $ (n, name)
      Nothing -> pure $ Varχ rn $ Name $ Left $ [name]
    Prd rn (OptBind (t, a)) ty -> do
      id <- fresh_id
      let n = (\text -> Name $ Right (id,text)) <$> t
          vars' = maybe vars (\t -> insert t id vars) t
      a' <- mapM (resolve_id' vars') a
      Prdχ rn (OptBind (n, a')) <$> resolve_id' vars' ty
    Abs rn (OptBind (t, ty)) e -> do
      id <- fresh_id
      let
        n = (\text -> Name $ Right (id,text)) <$> t 
        vars' = maybe vars (\t -> insert t id vars) t
      ty' <- mapM (resolve_id' vars') ty
      Absχ rn (OptBind (n, ty')) <$> resolve_id' vars' e
    App rn l r -> Appχ rn <$> (resolve_id' vars l) <*> (resolve_id' vars r)
