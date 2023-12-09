module Tui.Defaults.EditorKeymap
  ( default_keymap
  , module_keymap
  ) where

import Control.Monad.Except(MonadError)
import Lens.Micro
import Lens.Micro.Mtl
import qualified Data.Text.Zipper as Z
--import qualified Data.Text.Zipper.Generic as Z
import qualified Data.Text.Zipper.Generic.Words as Z

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

            -- Movement
            , ([(V.KChar 'k', [])], self %= move_up)
            , ([(V.KChar 'j', [])], self %= move_down)
            , ([(V.KChar 'h', [])], self %= move_left)
            , ([(V.KChar 'l', [])], self %= move_right)
            , ([(V.KChar 'b', [])], self %= applyEdit Z.moveWordLeft)
            , ([(V.KChar 'w', [])], self %= applyEdit Z.moveWordRight)
            , ([(V.KChar 'e', [])], self %= applyEdit Z.moveWordRight)
            , ([(V.KChar '0', [])], self %= applyEdit Z.gotoBOL)
            , ([(V.KChar '$', [])], self %= applyEdit Z.gotoEOL)

            , ([(V.KChar 'G', [])], self %= applyEdit Z.gotoEOF)
            , ([(V.KChar 'g', []), (V.KChar 'g', [])], self %= applyEdit Z.gotoBOF)

            -- Deletion
            , ([(V.KChar 'x', [])], self %= applyEdit Z.deleteChar)
            , ([(V.KChar 'd', []), (V.KChar 'w', [])], self %= applyEdit Z.deleteWord)
            , ([(V.KChar 'd', []), (V.KChar 'b', [])], self %= applyEdit Z.deletePrevWord)
            , ([(V.KChar 'd', []), (V.KChar '$', [])], self %= applyEdit Z.killToEOL)
            , ([(V.KChar 'd', []), (V.KChar '0', [])], self %= applyEdit Z.killToBOL)
            , ([(V.KChar 'd', []), (V.KChar 'd', [])], self %= applyEdit (Z.deleteChar . Z.killToEOL . Z.gotoBOL))

            -- Mode change
            , ([(V.KChar 'i', [])], self.mode .= Insert)
            , ([(V.KChar 'I', [])], self %= applyEdit Z.gotoBOL >> self.mode .= Insert)
            , ([(V.KChar 'A', [])], self %= applyEdit Z.gotoEOL >> self.mode .= Insert)
            , ([(V.KChar 'o', [])], self.mode .= Insert >> self %= applyEdit (Z.breakLine . Z.gotoEOL))
            , ([(V.KChar 'O', [])], self.mode .= Insert >> self %= applyEdit (Z.moveUp . Z.breakLine . Z.gotoBOL))

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
            -- Movement
  Normal -> [ ([(V.KUp, [])],    self %= move_up)
            , ([(V.KDown, [])],  self %= move_down)
            , ([(V.KLeft, [])],  self %= move_left)
            , ([(V.KRight, [])], self %= move_right)

            , ([(V.KChar 'k', [])], self %= move_up)
            , ([(V.KChar 'j', [])], self %= move_down)
            , ([(V.KChar 'h', [])], self %= move_left)
            , ([(V.KChar 'l', [])], self %= move_right)
            , ([(V.KChar 'b', [])], self %= applyEdit Z.moveWordLeft)
            , ([(V.KChar 'w', [])], self %= applyEdit Z.moveWordRight)
            , ([(V.KChar 'e', [])], self %= applyEdit Z.moveWordRight)
            , ([(V.KChar '0', [])], self %= applyEdit Z.gotoBOL)
            , ([(V.KChar '$', [])], self %= applyEdit Z.gotoEOL)

            , ([(V.KChar 'G', [])], self %= applyEdit Z.gotoEOF)
            , ([(V.KChar 'g', []), (V.KChar 'g', [])], self %= applyEdit Z.gotoBOF)

            -- Deletion
            , ([(V.KChar 'x', [])], self %= applyEdit Z.deleteChar)
            , ([(V.KChar 'd', []), (V.KChar 'w', [])], self %= applyEdit Z.deleteWord)
            , ([(V.KChar 'd', []), (V.KChar 'b', [])], self %= applyEdit Z.deletePrevWord)
            , ([(V.KChar 'd', []), (V.KChar '$', [])], self %= applyEdit Z.killToEOL)
            , ([(V.KChar 'd', []), (V.KChar '0', [])], self %= applyEdit Z.killToBOL)
            , ([(V.KChar 'd', []), (V.KChar 'd', [])], self %= applyEdit (Z.deleteChar . Z.killToEOL . Z.gotoBOL))

            -- Mode change
            , ([(V.KChar 'i', [])], self.mode .= Insert)
            , ([(V.KChar 'I', [])], self %= applyEdit Z.gotoBOL >> self.mode .= Insert)
            , ([(V.KChar 'A', [])], self %= applyEdit Z.gotoEOL >> self.mode .= Insert)
            , ([(V.KChar 'o', [])], self.mode .= Insert >> self %= applyEdit (Z.breakLine . Z.gotoEOL))
            , ([(V.KChar 'O', [])], self.mode .= Insert >> self %= applyEdit (Z.moveUp . Z.breakLine . Z.gotoBOL))

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
