{-# OPTIONS_GHC -XImpredicativeTypes #-}
module Tui.Editor
  ( Editor(..)
  -- lenses
  , keyActions
  , mode

  , editor
  , draw
  , getText
  , applyEdit
  , handleEvent
  , EditMode(..)

  , move_left
  , move_right
  , move_up
  , move_down
  ) where

import Data.Text (Text, pack)
import qualified Data.Text.Zipper as Z
import Data.Text.Zipper (TextZipper)
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl

import qualified Brick.Types as T
import qualified Brick.Widgets.Edit as E
import Brick.Widgets.Core (str)
import qualified Graphics.Vty as V

import Tui.Unicode  
import Tui.Keymap

data Editor s id = Editor
  { _brickEditor :: E.Editor String id
  , _charInputState :: Maybe [Char]

  -- Check for focus
  , _label :: id
  , _keyActions :: Lens' s (Editor s id) -> EditMode -> Keymap (T.EventM id s ())
  , _keyState :: [KeyEvent]
  , _mode :: EditMode
  }

data EditMode = Normal | Insert | Select | Structural
  deriving (Eq, Ord, Show)

$(makeLenses ''Editor)

editor :: id -> (Lens' s (Editor s id) -> EditMode -> Keymap (T.EventM id s ())) -> (Editor s id)
editor id initial_keymap = Editor
  { _brickEditor = E.editor id Nothing ""  
  , _charInputState = Nothing
  , _label = id
  , _keyActions = initial_keymap
  , _keyState = []
  , _mode = Normal
  }

draw :: (Ord id, Show id) => Editor s id -> id -> T.Widget id
draw st focus =
  E.renderEditor (str . unlines) (st^.label == focus) (st^.brickEditor)

handleEvent :: forall ev s id. Eq id => T.BrickEvent id ev -> Lens' s (Editor s id) -> T.EventM id s ()
handleEvent ev self = case ev of
  (T.VtyEvent (V.EvKey k mods)) -> do 
    this <- use self :: T.EventM id s (Editor s id)
    keys <- use (self.keyState)
    cmode <- use (self.mode)
    let (st', maction) = keypress ((this^.keyActions) self cmode) keys (k, mods)
    self.keyState .= st'
    case maction of 
      Just action -> action
      Nothing
        | cmode == Insert -> case st' of
            [] -> case (k, mods)  of 
              (V.KChar c, []) -> do
                char_st <- use (self.charInputState)
                case char_st of
                  Nothing | c == ';' -> self.charInputState .= Just []
                          | otherwise -> zoom (self.brickEditor) $ E.handleEditorEvent ev
                  Just cs ->
                    let (cs', func) = (char_update c cs)
                    in do self.charInputState .= cs'
                          self %= applyEdit func
              _ -> zoom (self.brickEditor) $ E.handleEditorEvent ev
            _ -> pure ()
        | otherwise -> pure ()
  _ -> zoom (self.brickEditor) $ E.handleEditorEvent ev

getText :: Editor s id -> Text 
getText = pack . unlines . E.getEditContents . _brickEditor

applyEdit :: (TextZipper String -> TextZipper String) -> Editor s n -> Editor s n
applyEdit f = (brickEditor %~ E.applyEdit f)

move_up :: Editor s n -> Editor s n 
move_up = applyEdit Z.moveUp

move_down :: Editor s n -> Editor s n 
move_down = applyEdit Z.moveDown

move_right :: Editor s n -> Editor s n 
move_right = applyEdit Z.moveRight

move_left :: Editor s n -> Editor s n 
move_left = applyEdit Z.moveLeft

-- move_word :: Editors n -> Editor s n
-- move_word 
