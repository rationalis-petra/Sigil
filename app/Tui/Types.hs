module Tui.Types
  ( InteractiveState(..)
  , focus
  , editorState
  , outputState
  , paletteState
  , paletteAction
  , loadedPackages
  , packageImports
  , availableModules
  , location
  , packageIx
  , packageImportsIx
  , moduleIx
  , importIx
  , interpreterState
  , NavLoc(..)
  , ID(..)
  , Dir(..)
  ) where

import Data.Text

import Lens.Micro.TH
--import Brick.Widgets.Edit
import qualified Brick.Types as T

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax (ImportDef)
import Sigil.Concrete.Internal (InternalModule)

import Tui.Editor (Editor)  

data InteractiveState s = InteractiveState
  { _focus :: ID
  -- text editor
  , _editorState :: Editor (InteractiveState s) ID

  -- output
  , _outputState :: String

  -- palette 
  , _paletteState :: Editor (InteractiveState s) ID
  , _paletteAction :: Text -> T.EventM ID (InteractiveState s) ()

  -- session
  , _loadedPackages :: [Text]
  , _packageImports :: [Text]
  , _availableModules :: [Path]

  -- 
  , _location :: (Text, Maybe InternalModule, [ImportDef])

  -- side panel
  , _packageIx :: Int
  , _packageImportsIx :: Int
  , _moduleIx :: Int
  , _importIx :: Int

  -- interpreter
  , _interpreterState :: s
  }

data NavLoc = NavPackage | NavPackImport | NavModule | NavEntry
  deriving (Ord, Show, Eq)
  
data ID = Input | Navigation NavLoc | Output | Palette
  deriving (Ord, Show, Eq)

data Dir = DUp | DDown | DLeft | DRight
  deriving (Eq, Ord, Show)

$(makeLenses ''InteractiveState)
