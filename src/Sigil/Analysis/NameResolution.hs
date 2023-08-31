module Sigil.Analysis.NameResolution
  ( ResolveTo(..)
  , resolve_closed
  ) where


import Prelude hiding (lookup)
import Control.Lens
import Data.Map (Map, lookup, insert, empty)
import Data.Text (Text)

import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment hiding (Environment(..)) 

import Sigil.Concrete.Parsed
import Sigil.Concrete.Resolved


{------------------------------- ID GENERATION ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

class ResolveTo a b | a -> b where
  resolve :: MonadGen m => Map Text Integer -> a -> m b


resolve_closed :: (MonadGen m, ResolveTo a b) => a -> m b
resolve_closed = resolve empty
  

instance ResolveTo ParsedCore ResolvedCore where
  resolve vars term = case term of 
    Core -> pure $ Coreχ ()
    Uni rn n -> pure $ Uniχ rn n
    Var rn name -> case lookup name vars of
      Just n -> pure $ Varχ rn $ Name $ Right (n, name)
      Nothing -> pure $ Varχ rn $ Name $ Left [name]
    Prd rn (OptBind (t, a)) ty -> do
      id <- fresh_id
      let n = (\text -> Name $ Right (id,text)) <$> t
          vars' = maybe vars (\t -> insert t id vars) t
      a' <- mapM (resolve vars) a
      Prdχ rn (OptBind (n, a')) <$> resolve vars' ty
    Abs rn (OptBind (t, ty)) e -> do
      id <- fresh_id
      let
        n = (\text -> Name $ Right (id,text)) <$> t 
        vars' = maybe vars (\t -> insert t id vars) t
      ty' <- mapM (resolve vars) ty
      Absχ rn (OptBind (n, ty')) <$> resolve vars' e
    App rn l r -> Appχ rn <$> resolve vars l <*> resolve vars r


instance ResolveTo ParsedDef ResolvedDef where
  resolve vars def = case def of 
    Mutualχ rn defs -> do
      (binds', vars') <- resolve_binds vars (map fst defs)
      defs' <- mapM (resolve vars' . snd) defs
      
      pure $ Mutualχ rn (zip binds' defs')
      where 
        resolve_binds :: MonadGen m => Map Text Integer -> [OptBind Text ParsedCore] -> m ([OptBind Name ResolvedCore], Map Text Integer)
        resolve_binds vars ((OptBind (t, a)):bs) =  do
          id <- fresh_id
          let  n = Name . Right . (id, ) <$> t
               vars' = maybe vars (\t -> insert t id vars) t
          a' <- mapM (resolve vars) a
          (bs', vars'') <- resolve_binds vars' bs
          pure (OptBind (n, a') : bs', vars'')
        resolve_binds vars [] = pure ([], vars)
      
    SigDefχ {} -> error "have not implemented ResolveTo for SigDefχ"
    IndDefχ {} -> error "have not implemented ResolveTo for IndDefχ"

instance ResolveTo ParsedModule ResolvedModule where
  -- TODO: interface with environment somehow? (based on imports/exports)
  resolve vars modul = do
    defs' <- mapM (resolve vars) (modul^.module_defs)
    pure $ (module_defs .~ defs') modul
