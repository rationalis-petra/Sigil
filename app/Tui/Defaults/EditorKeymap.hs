module Tui.Defaults.EditorKeymap
  ( default_keymap
  , module_keymap
  ) where

import Control.Monad.Except(MonadError)
import Lens.Micro
import Lens.Micro.Mtl

import Prettyprinter.Render.Sigil (SigilDoc)
import qualified Graphics.Vty as V
import qualified Brick.Types as T
import Brick.Main (halt)

import Sigil.Abstract.Names (Name, MonadGen)
import Sigil.Abstract.Environment (Environment)
import Sigil.Concrete.Internal (InternalCore)
import Sigil.Interpret.Interpreter

import Tui.Types
import Tui.Interaction
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


module_keymap :: forall m e s t id. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
                    Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t
              -> Lens' (InteractiveState s) (Editor (InteractiveState s) id) -> EditMode -> Keymap (T.EventM id (InteractiveState s) ())
module_keymap interpreter self = \case 
  Normal -> [ ([(V.KUp, [])],    self %= move_up)
            , ([(V.KDown, [])],  self %= move_down)
            , ([(V.KLeft, [])],  self %= move_left)
            , ([(V.KRight, [])], self %= move_right)

            , ([(V.KChar 'k', [])], self %= move_up)
            , ([(V.KChar 'j', [])], self %= move_down)
            , ([(V.KChar 'h', [])], self %= move_left)
            , ([(V.KChar 'l', [])], self %= move_right)

            , ([(V.KChar 'i', [])], self.mode .= Insert)

            -- Evaluate
            , ([(V.KChar ' ', []), (V.KChar 'e', [])], eval_text interpreter (getText . view self))
            , ([(V.KChar ' ', []), (V.KChar 'f', [])], load_file interpreter)
            , ([(V.KChar ' ', []), (V.KChar 'i', [])], add_import)

            -- Quit
            , ([(V.KChar ' ', []), (V.KChar 'q', []), (V.KChar 'q', [])], halt)
            ]
  Insert -> [ ([(V.KEsc, [])],    self.mode .= Normal)
            ]
  Select -> []
  Structural -> []
