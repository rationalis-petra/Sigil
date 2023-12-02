module Tui.Defaults.EditorKeymap (default_keymap) where

import Lens.Micro
import Lens.Micro.Mtl

import qualified Graphics.Vty as V
import qualified Brick.Types as T
import Brick.Main (halt)

import Tui.Editor
import Tui.Keymap

default_keymap :: Lens' s (Editor s id) -> EditMode -> Keymap (T.EventM id s ())
default_keymap self = \case 
  Normal -> [ ([(V.KUp, [])],    self %= move_up)
            , ([(V.KDown, [])],  self %= move_down)
            , ([(V.KLeft, [])],  self %= move_left)
            , ([(V.KRight, [])], self %= move_right)

            , ([(V.KChar 'k', [])], self %= move_up)
            , ([(V.KChar 'j', [])], self %= move_down)
            , ([(V.KChar 'h', [])], self %= move_left)
            , ([(V.KChar 'l', [])], self %= move_right)

            , ([(V.KChar 'i', [])], self.mode .= Insert)

            -- Quit
            , ([(V.KChar ' ', []), (V.KChar 'q', []), (V.KChar 'q', [])], halt)
            ]
  Insert -> [ ([(V.KEsc, [])],    self.mode .= Normal)
            ]
  Select -> []
  Structural -> []
