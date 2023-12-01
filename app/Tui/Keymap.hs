module Tui.Keymap
  ( Keymap
  , keypress) where

import Data.List (isPrefixOf)

import qualified Graphics.Vty as V


type Keymap a = [([V.Key], a)]

-- keymap :: KeyMap (T.EventM ID (InteractiveState s) ())
-- keymap = 
  
keypress :: Keymap a -> [V.Key] -> V.Key -> Maybe (Either [V.Key] a)
keypress keymap keys key = case filter (isPrefixOf (keys <> [key]) . fst) keymap of 
  [] -> Nothing 
  [(str, out)]
    | str == keys <> [key] -> Just $ Right out
    | otherwise -> Just (Left $ keys <> [key])
  _ -> Just (Left $ keys <> [key])
