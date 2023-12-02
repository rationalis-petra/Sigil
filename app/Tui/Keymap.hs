module Tui.Keymap
  ( Keymap
  , KeyEvent
  , keypress) where

import Data.List (isPrefixOf)

import qualified Graphics.Vty as V

type KeyEvent = (V.Key, [V.Modifier])

type Keymap a = [([KeyEvent], a)]

-- keymap :: KeyMap (T.EventM ID (InteractiveState s) ())
-- keymap = 
  
keypress :: Keymap a -> [KeyEvent] -> KeyEvent -> ([KeyEvent], Maybe a)
keypress keymap keys key = case filter (isPrefixOf (keys <> [key]) . fst) keymap of 
  [] -> ([], Nothing)
  [(str, out)]
    | str == keys <> [key] -> ([], Just out)
    | otherwise -> (keys <> [key], Nothing)
  _ -> (keys <> [key], Nothing)
