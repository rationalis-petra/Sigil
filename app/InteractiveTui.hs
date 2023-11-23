module InteractiveTui
  ( InteractiveTuiOpts(..)
  , interactive_tui ) where

import Prelude hiding (mod, getLine, putStr, putStrLn, readFile, null)

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
import Data.Text.Zipper (insertChar, insertMany)
import Data.List (isPrefixOf)
import Data.List.NonEmpty (NonEmpty((:|)))

import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec hiding (parse, runParser)
import Text.Megaparsec.Char as C
import qualified Graphics.Vty as V
import qualified Brick.AttrMap as A
import qualified Brick.Types as T
import Brick.Widgets.Core (joinBorders, str, hBox, vBox)
import Brick.Widgets.Border (border, hBorder, vBorder)
import Brick.Widgets.Edit
import Brick.Main
import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Parse.Lexer
import Sigil.Interpret.Interpreter
import Sigil.Concrete.Internal (InternalCore)

import InterpretUtils  

data InteractiveTuiOpts = InteractiveTuiOpts
  deriving (Show, Read, Eq)

data InteractiveState s = InteractiveState
  { _imports :: [ImportDef]
  , _focus :: ID
  , _editorState :: Editor String ID
  , _charInputState :: Maybe [Char]
  , _outputState :: String
  , _loadedModules :: [Path]
  , _interpreterState :: s
  }
  deriving Show

data ID = Input | Module | Output
  deriving (Ord, Show, Eq)

$(makeLenses ''InteractiveState)


interactive_tui :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> InteractiveTuiOpts -> IO ()
interactive_tui interpreter _ = do
  let app = App { appDraw = draw
                , appChooseCursor  = choose_cursor
                , appHandleEvent = app_handle_event interpreter
                , appStartEvent = return ()
                , appAttrMap = const (A.attrMap V.defAttr [])
                }
      initial_state = InteractiveState
        { _imports = []
        , _focus = Input
        , _editorState = editor Input Nothing ""
        , _charInputState = Nothing
        , _outputState = ""
        , _loadedModules = []
        , _interpreterState = (start_state interpreter)
        }
  void $ defaultMain app initial_state


draw :: InteractiveState s -> [T.Widget ID]
draw st = [joinBorders . border $ hBox
          [ vBox [(renderEditor (str . unlines) True (st^.editorState))
                 , hBorder 
                 , str "Output:"
                 , str (st^.outputState)]
          , vBorder, vBox ([str "loaded modules"] <> map (str . ("  " <>) .  show . pretty) (st^.loadedModules)
                           <> [hBorder]
                            <> [str "module repl", str "  import"] <> map (str . ("    " <>) . show . pretty) (st^.imports))]]

choose_cursor :: InteractiveState s -> [T.CursorLocation ID] -> Maybe (T.CursorLocation ID)
choose_cursor st locs = find (liftEq (==) (Just $ st^.focus) . T.cursorLocationName) locs

app_handle_event :: forall m e s t ev. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
                    Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> T.BrickEvent ID ev -> T.EventM ID (InteractiveState s) ()
app_handle_event interpreter = \case
  (T.VtyEvent (V.EvKey V.KEsc [])) -> halt

  -- Evaluate Playground
  (T.VtyEvent (V.EvKey (V.KChar 'e') [V.MCtrl])) -> do
    istate <- use interpreterState
    editor <- use editorState
    imp <- use imports
    let text = pack $ unlines $ getEditContents editor
    (result, state') <- liftIO $ (run interpreter) istate (eval_expr interpreter imp text)
    interpreterState .= state'
    case result of
      Right (val, ty) -> do
        outputState .= (show $ vsep [ "val:" <+> nest 2 (pretty val)
                                   , "type:" <+> nest 2 (pretty ty) ])
      Left err -> outputState .= show err

  -- Load File
  (T.VtyEvent (V.EvKey (V.KChar 'f') [V.MCtrl])) -> do
    istate <- use interpreterState
    editor <- use editorState
    let filename = strip . pack . unlines $ getEditContents editor 
    text <- liftIO $ readFile (unpack filename)
    (result, istate') <- liftIO $ (run interpreter) istate $ do
      mod <- eval_mod interpreter filename text
      (intern_module interpreter) (mod^.module_header) mod
      pure mod
    case result of
      Left err -> do
        interpreterState .= istate'
        outputState .= show err
      _ -> do 
        (modules, istate'') <- liftIO $ (run interpreter) istate' $ (get_modules interpreter)
        interpreterState .= istate''
        case modules of
          Left err -> outputState %= (<> ("\n" <> show err)) -- TODO: change!!
          Right val -> loadedModules .= val

  -- Do Import
  (T.VtyEvent (V.EvKey (V.KChar 'b') [V.MCtrl])) -> do
    editor <- use editorState
    let import_statement = strip . pack . unlines $ getEditContents editor
    case Megaparsec.runParser pImport "import" import_statement of
      Left _ -> outputState .= "import parser failure"
      Right val -> imports %= (val :)
    
  -- Do definition
  -- (T.VtyEvent (V.EvKey (V.KChar 'd') [V.MCtrl])) -> do

  ev -> do
    f <- use focus
    case f of 
      Input -> handle_input_event ev
      _ -> pure ()

handle_input_event :: T.BrickEvent ID e -> T.EventM ID (InteractiveState s) ()
handle_input_event ev = case ev of
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
    editorState %= applyEdit (insertMany (cs <> [c]))
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

  , ("A" , '⍝')
  , ("e|", '⋳')
  , ("|e", '⋻')

  , ("to", '→')
  , ("fm", '←')
  , ("up", '↑')
  , ("dn", '↓')

  , ("le", '⮜')
  , ("de", '≜')
  , ("rc", 'ᛉ')
  , ("rr", 'ᛯ')
  , ("ri", 'ᛣ')

  , ("ga", 'α')
  , ("gl", 'λ')
  , ("gm", 'μ')
  , ("gf", 'φ')
  , ("gn", 'ν')
  , ("gc", 'ψ')

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
