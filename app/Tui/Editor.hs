module Tui.Editor
  ( Editor(..)
  , editor
  , draw
  , getText
  , applyEdit
  , handleEvent
  ) where

import Control.Monad.State (modify)
import Data.Text (Text, pack)
import Data.Text.Zipper (TextZipper)
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl

import qualified Brick.Types as T
import qualified Brick.Widgets.Edit as E
import Brick.Widgets.Core (str)
import qualified Graphics.Vty as V

import Tui.Unicode  

data Editor id = Editor
  { _brickEditor :: E.Editor String id
  , _charInputState :: Maybe [Char]

  -- Check for focus
  , _label :: id
  }

$(makeLenses ''Editor)

editor :: id -> Editor id
editor id = Editor
  { _brickEditor = E.editor id Nothing ""  
  , _charInputState = Nothing
  , _label = id
  }

draw :: (Ord id, Show id) => Editor id -> id -> T.Widget id
draw st focus =
  E.renderEditor (str . unlines) (st^.label == focus) (st^.brickEditor)

handleEvent :: Eq id => T.BrickEvent id ev -> T.EventM id (Editor id) ()
handleEvent ev = case ev of
  T.VtyEvent (V.EvKey (V.KChar c) []) -> do 
    char_st <- use charInputState
    case char_st of
      Nothing | c == ';' -> charInputState .= Just []
              | otherwise -> zoom brickEditor $ E.handleEditorEvent ev
      Just cs ->
        let (cs', func) = (char_update c cs)
        in do charInputState .= cs'
              modify $ applyEdit func
        
  _ -> zoom brickEditor $ E.handleEditorEvent ev
  

getText :: Editor id -> Text 
getText = pack . unlines . E.getEditContents . _brickEditor

applyEdit :: (TextZipper String -> TextZipper String)
          -> Editor n
          -> Editor n
applyEdit f = (brickEditor %~ E.applyEdit f)
