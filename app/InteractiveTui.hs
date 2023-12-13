{-# OPTIONS_GHC -Wno-type-defaults #-}
module InteractiveTui
  ( InteractiveTuiOpts(..)
  , interactive_tui ) where

import Prelude hiding (mod, getLine, putStr, putStrLn, readFile, null)

import Control.Monad (void)
import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (liftIO)
import Lens.Micro
-- import Lens.Micro.TH
import Lens.Micro.Mtl
import Data.Functor.Classes (liftEq)
import Data.Foldable (find)
import Data.Text (strip)
import Data.Text.Zipper (clearZipper)
import qualified Data.Map as Map

import qualified Graphics.Vty as V
import qualified Brick.AttrMap as A
import qualified Brick.Types as T
import Brick.Widgets.Core (joinBorders, str, hBox, vBox, hLimit, vLimit, withAttr)
import Brick.Widgets.Border (border, hBorder, vBorder)
import Brick.Widgets.Center (centerLayer)
import Brick.Main
import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Interpret.Interpreter
import Sigil.Concrete.Internal (InternalCore)

import qualified Tui.Editor as Editor
import Tui.Types
import Tui.Defaults.EditorKeymap

data InteractiveTuiOpts = InteractiveTuiOpts
  deriving (Show, Read, Eq)


interactive_tui :: forall m e s t f. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f -> InteractiveTuiOpts -> IO ()
interactive_tui interpreter _ = do
  let app = App { appDraw = draw
                , appChooseCursor  = choose_cursor
                , appHandleEvent = app_handle_event interpreter
                , appStartEvent = do
                    istate <- use interpreterState
                    (merr, state')  <- liftIO $ (run interpreter) istate $ do
                      (intern_package interpreter)
                        "sigil-user" (Package
                                      (PackageHeader "sigil-user" [] (0,0,0))
                                      (MTree Map.empty))
                      packages <- get_available_packages interpreter
                      modules <- get_available_modules interpreter "sigil-user"
                      pure $ (packages, modules)
                      
                    case merr of
                      Right (packages, modules) -> do
                        availableModules .= modules
                        loadedPackages .= packages
                      Left err -> outputState .= show ("error in initialization:" <+> err)
                    interpreterState .= state'
                , appAttrMap =
                  const (A.attrMap V.defAttr
                         [ (A.attrName "title", V.withStyle V.defAttr V.bold)
                         , (A.attrName "emphasis", V.withStyle V.defAttr V.italic)
                         , (A.attrName "selected",
                            V.withForeColor
                             (V.withBackColor V.defAttr (V.rgbColor 197 200 198))
                             (V.rgbColor 29 31 33))
                         , (A.attrName "green",
                            V.withForeColor V.defAttr
                             (V.rgbColor 181 189 104))
                         , (A.attrName "yellow",
                            V.withForeColor V.defAttr
                             (V.rgbColor 240 198 116))
                         , (A.attrName "red",
                            V.withForeColor V.defAttr
                             (V.rgbColor 204 102 102))])
                }
            
      initial_state = InteractiveState
        { _focus = Input
        , _editorState = Editor.editor Input (module_keymap interpreter)

        , _outputState = ""

        -- session
        , _location = ("sigil-user", Nothing, [])
        , _availableModules = []
        , _loadedPackages = []
        , _packageIx = 0
        , _moduleIx = 0
        , _importIx = 0

        , _interpreterState = (start_state interpreter)

        -- palette
        , _paletteState = (Editor.mode .~ Editor.Insert) (Editor.editor Palette default_keymap)
        , _paletteAction = pure . const ()
        }
  void $ defaultMain app initial_state


draw :: InteractiveState s -> [T.Widget ID]
draw st =
  let main_panel =
        joinBorders . border $ hBox
          [ vBox [(Editor.draw True (st^.editorState) Input)
                 , hBorder 
                 , withAttr (A.attrName "title") (str "Output")
                 , str (st^.outputState)]
          , vBorder, module_browser]

      module_browser = 
        vBox ([withAttr (A.attrName "title") (str "Packages")]
              <> packagesList
              <> [hBorder]
              <> [withAttr (A.attrName "title") (str "Modules")]
              <> modulesList
              <> [hBorder]
              <> importsWidget)

      packagesList =
        if (st^.focus) == Navigation NavPackage
        then zipWith (\s i -> (if i == st^.packageIx then withAttr (A.attrName "selected")
                                else (if s == st^.location._1 then withAttr (A.attrName "emphasis") else id))
                              (str . ("  " <>) .  show . pretty $ s))
             (st^.loadedPackages) [0..]

        else fmap (\s -> (if (s == st^.location._1) then withAttr (A.attrName "emphasis") else id)
                    (str . ("  " <>) .  show . pretty $ s)) (st^.loadedPackages)
             
      modulesList =
        if (st^.focus) == Navigation NavModule
        then zipWith (\s i -> (if i == st^.moduleIx then withAttr (A.attrName "selected")
                                else (if Just s == fmap _module_header (st^.location._2) then withAttr (A.attrName "emphasis") else id))
                              (str . ("  " <>) .  show . pretty $ s))
             (st^.availableModules) [0..]
        else fmap (\s -> (if (Just s == fmap _module_header (st^.location._2)) then withAttr (A.attrName "emphasis") else id)
                    (str . ("  " <>) .  show . pretty $ s)) (st^.availableModules)

      importsWidget =
        case (st^.location._2) of
          Just mdle -> [str $ show $ pretty mdle]
          Nothing -> [withAttr (A.attrName "title") (str "Imports")] <> importsList

      importsList = 
        if (st^.focus) == Navigation NavEntry
        then zipWith (\s i -> (if i == st^.importIx then withAttr (A.attrName "selected") else id)
                              (str . ("  " <>) .  show . pretty $ s))
             (st^.location._3) [0..]
        else fmap (str . ("  " <>) .  show . pretty) (st^.location._3)
  
      palette = centerLayer
        $ border
        $ hLimit 60
        $ vLimit 1
        $ Editor.draw False (st^.paletteState) Palette
      
  in case (st^.focus) of 
    Palette -> [palette, main_panel] -- (palette : main_panel)
    _ -> [main_panel]

change_focus :: Dir -> ID -> ID
change_focus DUp    (Navigation loc)
  | loc == NavPackage = Navigation NavPackage
  | loc == NavModule  = Navigation NavPackage
  | loc == NavEntry   = Navigation NavModule
change_focus DDown  (Navigation loc)
  | loc == NavPackage = Navigation NavModule
  | loc == NavModule  = Navigation NavEntry
  | loc == NavEntry   = Navigation NavEntry
change_focus DLeft  (Navigation _)  = Input
change_focus DRight Input = Navigation NavModule 
change_focus _ v = v

choose_cursor :: InteractiveState s -> [T.CursorLocation ID] -> Maybe (T.CursorLocation ID)
choose_cursor st locs = find (liftEq (==) (Just $ st^.focus) . T.cursorLocationName) locs

app_handle_event :: forall m e s t f ev. Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f
  -> T.BrickEvent ID ev -> T.EventM ID (InteractiveState s) ()
app_handle_event _ = \case
  (T.VtyEvent (V.EvKey V.KUp    [V.MCtrl])) -> focus %= change_focus DUp
  (T.VtyEvent (V.EvKey V.KDown  [V.MCtrl])) -> focus %= change_focus DDown
  (T.VtyEvent (V.EvKey V.KLeft  [V.MCtrl])) -> focus %= change_focus DLeft
  (T.VtyEvent (V.EvKey V.KRight [V.MCtrl])) -> focus %= change_focus DRight

  ev -> do
    f <- use focus
    case f of 
      Input -> Editor.handleEvent ev editorState
      Palette -> handle_palette_event ev
      Navigation loc -> handle_nav_event loc ev
      _ -> pure ()

handle_nav_event :: NavLoc -> T.BrickEvent ID e -> T.EventM ID (InteractiveState s) ()
handle_nav_event loc ev =
  let ix :: Lens' (InteractiveState s) Int
      ix = case loc of   
        NavPackage -> packageIx
        NavModule ->  moduleIx
        NavEntry ->   importIx
      inc = do
        upper <- case loc of 
          NavPackage -> length <$> use loadedPackages
          NavModule -> length <$> use availableModules
          NavEntry -> length <$> use (location._3)
        ix %= min upper . (+ 1)
      dec = ix %= max 0 . (\x -> x - 1)

      del = do
        ixval <- use ix
        case loc of 
          NavPackage -> pure () -- TODO: add action
          NavModule -> pure () -- TODO: add action
          NavEntry -> do
            (location._3) %= fmap snd . filter ((/= ixval) . fst) . zip [0..]
            upper <- length <$> use (location._3)
            importIx %= min upper

  in case ev of
    (T.VtyEvent (V.EvKey (V.KUp)       [])) -> dec
    (T.VtyEvent (V.EvKey (V.KDown)     [])) -> inc 
    (T.VtyEvent (V.EvKey (V.KChar 'd') [])) -> del
    _ -> pure ()

handle_palette_event :: T.BrickEvent ID e -> T.EventM ID (InteractiveState s) ()
handle_palette_event ev = case ev of 
  (T.VtyEvent (V.EvKey V.KEnter [])) -> do 
    palette <- use paletteState
    action <- use paletteAction
    paletteState %= Editor.applyEdit clearZipper
    (paletteState.Editor.mode) .= Editor.Insert
    action (strip $ Editor.getText palette)
    focus .= Input
  (T.VtyEvent (V.EvKey (V.KChar 'g') [V.MCtrl])) -> do 
    paletteState %= Editor.applyEdit clearZipper
    (paletteState.Editor.mode) .= Editor.Insert
    focus .= Input
   
  _ -> Editor.handleEvent ev paletteState
