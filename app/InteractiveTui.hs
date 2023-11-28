{-# OPTIONS_GHC -Wno-type-defaults #-}
module InteractiveTui
  ( InteractiveTuiOpts(..)
  , interactive_tui ) where

import Prelude hiding (mod, getLine, putStr, putStrLn, readFile, null)

import qualified Control.Exception as Exception
import Control.Monad (void)
import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (liftIO)
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Data.Functor.Classes (liftEq)
import Data.Foldable (find)
import Data.Text (Text, pack, unpack, strip)
import Data.Text.IO (readFile)
import Data.Text.Zipper (insertChar, insertMany, clearZipper)
import Data.List (isPrefixOf)
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Map as Map
import System.IO.Error (isDoesNotExistError)

import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec hiding (parse, runParser)
import Text.Megaparsec.Char as C
import qualified Graphics.Vty as V
import qualified Brick.AttrMap as A
import qualified Brick.Types as T
import Brick.Widgets.Core (joinBorders, str, hBox, vBox, hLimit, vLimit, withAttr)
import Brick.Widgets.Border (border, hBorder, vBorder)
import Brick.Widgets.Center (centerLayer)
import Brick.Widgets.Edit
import Brick.Main
import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Concrete.Internal (InternalModule)
import Sigil.Parse.Lexer
import Sigil.Interpret.Interpreter
import Sigil.Concrete.Internal (InternalCore)

import InterpretUtils  

data InteractiveTuiOpts = InteractiveTuiOpts
  deriving (Show, Read, Eq)

data InteractiveState s = InteractiveState
  { _focus :: ID
  -- text editor
  , _editorState :: Editor String ID
  , _charInputState :: Maybe [Char]

  -- output
  , _outputState :: String

  -- palette 
  , _paletteState :: Editor String ID
  , _paletteAction :: Text -> T.EventM ID (InteractiveState s) ()

  -- session
  , _loadedPackages :: [Text]
  , _availableModules :: [Path]
  , _location :: (Text, Maybe InternalModule, [ImportDef])

  -- side panel
  , _packageIx :: Int
  , _moduleIx :: Int
  , _importIx :: Int

  -- interpreter
  , _interpreterState :: s
  }

data NavLoc = NavPackage | NavModule | NavEntry
  deriving (Ord, Show, Eq)
  
data ID = Input | Navigation NavLoc | Output | Palette
  deriving (Ord, Show, Eq)

data Dir = DUp | DDown | DLeft | DRight
  deriving (Eq, Ord, Show)

$(makeLenses ''InteractiveState)


interactive_tui :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> InteractiveTuiOpts -> IO ()
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
                             (V.rgbColor 29 31 33))])
                }
      initial_state = InteractiveState
        { _focus = Input
        , _editorState = editor Input Nothing ""
        , _charInputState = Nothing

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
        , _paletteState = editor Palette Nothing ""  
        , _paletteAction = pure . const ()
        }
  void $ defaultMain app initial_state


draw :: InteractiveState s -> [T.Widget ID]
draw st =
  let main_panel =
        joinBorders . border $ hBox
          [ vBox [(renderEditor (str . unlines) (st^.focus == Input) (st^.editorState))
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
        $ renderEditor (str . unlines) (st^.focus == Palette) (st^.paletteState)
      
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

-- data NavLoc = NavPackage | NavModule | NavEntry
--   deriving (Ord, Show, Eq)
  
-- data ID = Input | Navigation NavLoc | Output | Palette

choose_cursor :: InteractiveState s -> [T.CursorLocation ID] -> Maybe (T.CursorLocation ID)
choose_cursor st locs = find (liftEq (==) (Just $ st^.focus) . T.cursorLocationName) locs

app_handle_event :: forall m e s t ev. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
                    Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> T.BrickEvent ID ev -> T.EventM ID (InteractiveState s) ()
app_handle_event interpreter = \case
  (T.VtyEvent (V.EvKey V.KEsc [])) -> halt

  (T.VtyEvent (V.EvKey V.KUp    [V.MCtrl])) -> focus %= change_focus DUp
  (T.VtyEvent (V.EvKey V.KDown  [V.MCtrl])) -> focus %= change_focus DDown
  (T.VtyEvent (V.EvKey V.KLeft  [V.MCtrl])) -> focus %= change_focus DLeft
  (T.VtyEvent (V.EvKey V.KRight [V.MCtrl])) -> focus %= change_focus DRight

  ev -> do
    f <- use focus
    case f of 
      Input -> handle_editor_event interpreter ev
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
          NavEntry ->
            (location._3) %= fmap snd . filter ((/= ixval) . fst) . zip [0..]

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
    paletteState %= applyEdit clearZipper
    action (strip . pack . unlines $ getEditContents palette)
  _ -> zoom paletteState $ handleEditorEvent ev


handle_editor_event :: forall m e s t ev. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t  -> T.BrickEvent ID ev -> T.EventM ID (InteractiveState s) ()
handle_editor_event interpreter ev = case ev of
  -- Evaluate Playground
  (T.VtyEvent (V.EvKey (V.KChar 'e') [V.MCtrl])) -> do
    istate <- use interpreterState
    editor <- use editorState
    (pname, _, imports) <- use location
    let text = pack $ unlines $ getEditContents editor
    (result, state') <- liftIO $ (run interpreter) istate (eval_expr interpreter pname imports text)
    interpreterState .= state'
    case result of
      Right (val, ty) -> do
        outputState .= (show $ vsep [ "val:" <+> nest 2 (pretty val)
                                   , "type:" <+> nest 2 (pretty ty) ])
      Left err -> outputState .= show err

  -- Load File
  (T.VtyEvent (V.EvKey (V.KChar 'f') [V.MCtrl])) -> do
    focus .= Palette
    paletteAction .= (\filename -> do
      focus .= Input
      istate <- use interpreterState
      pkg_name <- use (location._1)
      out <- liftIO $ (Right <$> readFile (unpack filename)) `Exception.catch` (pure . Left)
      case out of 
        Right text -> do
          (result, istate') <- liftIO $ (run interpreter) istate $ do
            mod <- eval_mod interpreter pkg_name filename text
            (intern_module interpreter) pkg_name (mod^.module_header) mod
            pure mod
          case result of
            Left err -> do
              interpreterState .= istate'
              outputState .= show err
            _ -> do 
              (modules, istate'') <- liftIO $ (run interpreter) istate' $ (get_available_modules interpreter) pkg_name 
              interpreterState .= istate''
              case modules of
                Left err -> outputState %= (<> ("\n" <> show err)) -- TODO: change!!
                Right val -> availableModules .= val
        Left e
          | isDoesNotExistError e -> outputState .= ("file does not exist: " <> unpack filename)
          | otherwise -> outputState .= "IO error encountered reading file: " <> unpack filename)
                                     
    
  -- Do Import
  (T.VtyEvent (V.EvKey (V.KChar 'b') [V.MCtrl])) -> do
    focus .= Palette
    paletteAction .= (\import_statement -> do
      focus .= Input
      case Megaparsec.runParser pImport "import" import_statement of
        Left _ -> outputState .= "import parser failure"
        Right val -> (location._3) %= (val :))

  (T.VtyEvent (V.EvKey (V.KChar c) [])) -> do 
    char_st <- use charInputState
    case char_st of
      Nothing | c == ';' -> charInputState .= Just []
              | otherwise -> zoom editorState $ handleEditorEvent ev
      Just cs -> char_update c cs
  _ -> zoom editorState $ handleEditorEvent ev

char_update :: Char -> [Char] -> T.EventM ID (InteractiveState s) ()
char_update c cs = case filter (isPrefixOf (cs <> [c]) . fst) unicode_input_map of 
  [] -> do
    charInputState .= Nothing
    editorState %= applyEdit (insertMany ((';' : cs) <> [c]))
  [(str, out)]
    | str == cs <> [c] -> do
        editorState %= applyEdit (insertChar out)
        charInputState .= Nothing
    | otherwise -> charInputState .= Just (cs <> [c])
  _ -> charInputState .= Just (cs <> [c])
  
unicode_input_map :: [([Char], Char)]
unicode_input_map =
  [ ("sA", '𝔸')
  , ("sN", 'ℕ')
  , ("sU", '𝕌')
  , ("sZ", 'ℤ')

  -- numeric & algebraic operations 
  , (":-", '÷')
  , ("x" , '×')
  , ("*" , '⋅')
  , ("v/", '√')
  , ("^" , '∧')
  , ("-^", '⊼')
  , ("v" , '∨')
  , ("-v", '⊽')
  , ("v-", '⊻')
  , ("-.", '¬')

  -- equality & comparisons
  , ("~=" , '≃')
  , ("~==", '≅')
  , ("^=" , '≜')
  , ("/=" , '≠')
  , ("==" , '≡')
  , ("/==", '≢')
  , ("?=" , '≟')
  , ("o=" , '≗')
  , (">=" , '≥')
  , ("!=" , '≠')
  , ("<=" , '≤')

  -- Sigil specific
  , ("A" , '⍝')
  , ("e|", '⋳')
  , ("|e", '⋻')
  , ("le", '⮜')
  , ("ri", '⮞') 
  , ("de", '≜')
  , ("rc", 'ᛉ')
  , ("rr", 'ᛯ')
  , ("ri", 'ᛣ')

  -- arraos
  , ("to", '→')
  , ("fm", '←')
  , ("up", '↑')
  , ("dn", '↓')

  -- Subscripts
  , ("_0", '₀')
  , ("_1", '₁')
  , ("_2", '₂')
  , ("_3", '₃')
  , ("_4", '₄')
  , ("_5", '₅')
  , ("_6", '₆')
  , ("_7", '₇')
  , ("_8", '₈')
  , ("_9", '₉')
  , ("_=", '₌')
  , ("_-", '₋')
  , ("_+", '₊')
  , ("_a", 'ₐ')
  , ("_e", 'ₑ')
  , ("_h", 'ₕ')
  , ("_i", 'ᵢ')
  , ("_j", 'ⱼ')
  , ("_l", 'ₗ')
  , ("_m", 'ₘ')
  , ("_n", 'ₙ')
  , ("_o", 'ₒ')
  , ("_p", 'ₚ')
  , ("_r", 'ᵣ')
  , ("_s", 'ₛ')
  , ("_t", 'ₜ')
  , ("_u", 'ᵤ')
  , ("_v", 'ᵥ')
  , ("_x", 'ₓ')

  -- greek
  , ("ga", 'α')
  , ("gb", 'β')
  , ("gc", 'ψ')
  , ("gd", 'δ')
  , ("ge", 'ε')
  , ("gf", 'φ')
  , ("gg", 'γ')
  , ("gh", 'η')
  , ("gi", 'ι')
  , ("gj", 'ξ')
  , ("gk", 'κ')
  , ("gl", 'λ')
  , ("gm", 'μ')
  , ("gn", 'ν')
  , ("go", 'ο')
  , ("gp", 'π')
  , ("gr", 'ρ')
  , ("gs", 'σ')
  , ("gt", 'τ')
  , ("gu", 'θ')
  , ("gv", 'ω')
  , ("gw", 'ς')
  , ("gx", 'χ')
  , ("gy", 'υ')
  , ("gz", 'ζ')
  , ("gA", 'Α')
  , ("gB", 'Β')
  , ("gC", 'Ψ')
  , ("gD", 'Δ')
  , ("gE", 'Ε')
  , ("gF", 'Φ')
  , ("gG", 'Γ')
  , ("gH", 'Η')
  , ("gI", 'Ι')
  , ("gJ", 'Ξ')
  , ("gK", 'Κ')
  , ("gL", 'Λ')
  , ("gM", 'Μ')
  , ("gN", 'Ν')
  , ("gO", 'Ο')
  , ("gP", 'Π')
  , ("gR", 'R')
  , ("gS", 'Σ')
  , ("gT", 'Τ')
  , ("gU", 'Θ')
  , ("gV", 'Ω')
  , ("gW", 'Σ')
  , ("gX", 'Χ')
  , ("gY", 'Υ')
  , ("gZ", 'Ζ')

  ]

type TParser = Parsec Text Text

pImport :: TParser ImportDef
pImport = do
  let
    sep :: TParser a -> TParser b -> TParser [a]
    sep p separator = ((: []) <$> p <|> pure []) >>= \v ->
        (v <> ) <$> many (try (separator *> p))

  l <- sep anyvar (C.char '.' <* sc)
  path <- case l of 
    [] -> fail "import path must be nonempty"
    (x:xs) -> pure (Path $ x:|xs)
  modifier <- pModifier <|> pure ImSingleton
  pure $ Im (path, modifier)

pModifier :: TParser ImportModifier
pModifier = 
  const ImWildcard <$> (lexeme (C.char '.') *> symbol "(..)")
