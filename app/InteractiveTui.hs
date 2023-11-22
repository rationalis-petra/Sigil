module InteractiveTui
  ( InteractiveTuiOpts(..)
  , interactive_tui ) where

import Prelude hiding (mod, getLine, putStr, putStrLn, readFile, null)

import Control.Monad (void)
import Control.Monad.Except (MonadError, throwError, catchError)
import Control.Monad.IO.Class (liftIO)
--import Control.Lens (makeLenses, use, zoom, (^.))
--import Control.Lens.TH (zoom)
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Data.Functor.Classes (liftEq)
import Data.Foldable (find)
import Data.Text (Text, pack)
import Data.List (isPrefixOf)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Text.Zipper (insertChar, insertMany)

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
import Sigil.Abstract.Environment
import Sigil.Abstract.Syntax (ImportDef)
import Sigil.Parse
import Sigil.Analysis.NameResolution
import Sigil.Interpret.Interpreter
import Sigil.Analysis.Typecheck
import Sigil.Concrete.Internal (InternalCore)

newtype InteractiveTuiOpts = InteractiveTuiOpts
  { ifile :: Text
  }
  deriving (Show, Read, Eq)

data InteractiveState s = InteractiveState
  { _imports :: [ImportDef]
  , _focus :: ID
  , _editorState :: Editor String ID
  , _charInputState :: Maybe [Char]
  , _outputState :: String
  , _interpreterState :: s
  }
  deriving Show

data ID = Input | Module | Output
  deriving (Ord, Show, Eq)

$(makeLenses ''InteractiveState)

-- interactive_tui :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e)
--   => Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> InteractiveTuiOpts -> IO ()
--interactive_tui (Interpreter {..}) opts = do ...

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
        , _outputState = "output state"
        , _interpreterState = (start_state interpreter)
        }
  void $ defaultMain app initial_state


eval_play :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> Text -> m (InternalCore, InternalCore)
eval_play (Interpreter {..}) line = do
  env <- get_env ("repl" :| []) []
  precs <- get_precs ("repl" :| []) []
  resolution <- get_resolve ("repl" :| []) []
  parsed <- core precs "playground" line  -- TODO: eof??
  resolved <- resolve_closed (("unbound name" <+>) . pretty) resolution parsed
    `catchError` (throwError . (<+>) "Resolution:")
  (term, ty) <- infer (CheckInterp interp_eval interp_eq spretty) env resolved
    `catchError` (throwError . (<+>) "Inference:")
  norm <- interp_eval id env ty term
    `catchError` (throwError . (<+>) "Normalization:")
  pure (norm, ty)

  where
    interp_eval :: (SigilDoc -> SigilDoc) -> e (Maybe InternalCore, InternalCore) -> InternalCore -> InternalCore -> m InternalCore
    interp_eval f env ty val = do
      ty' <- reify ty
      val' <- reify val
      result <- eval f env ty' val'
      reflect result 
  
    interp_eq :: (SigilDoc -> SigilDoc) -> e (Maybe InternalCore, InternalCore) -> InternalCore -> InternalCore -> InternalCore -> m Bool
    interp_eq f env ty l r = do
      ty' <- reify ty
      l' <- reify l
      r' <- reify r
      norm_eq f env ty' l' r'

draw :: InteractiveState s -> [T.Widget ID]
draw st = [joinBorders . border $ hBox
          [ vBox [(renderEditor (str . unlines) True (st^.editorState))
                 , hBorder 
                 , str (st^.outputState)]
          , vBorder, vBox (str "module repl" : map (str . show) (st^.imports))]]

choose_cursor :: InteractiveState s -> [T.CursorLocation ID] -> Maybe (T.CursorLocation ID)
choose_cursor st locs = find (liftEq (==) (Just $ st^.focus) . T.cursorLocationName) locs

app_handle_event :: forall m e s t ev. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
                    Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> T.BrickEvent ID ev -> T.EventM ID (InteractiveState s) ()
app_handle_event interpreter = \case
  (T.VtyEvent (V.EvKey V.KEsc [])) -> halt
  (T.VtyEvent (V.EvKey (V.KChar 'e') [V.MCtrl])) -> do
    istate <- use interpreterState
    editor <- use editorState
    let text = pack $ unlines $ getEditContents editor
    (result, state') <- liftIO $ (run interpreter) istate (eval_play interpreter text)
    interpreterState .= state'
    case result of
      Right (val, ty) -> do
        outputState .= (show $ vsep [ "val:" <+> nest 2 (pretty val)
                                   , "type:" <+> nest 2 (pretty ty) ])
      Left err -> outputState .= show err
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
  [ ("sU", '𝕌')

  , ("le", '⮜')
  , ("de", '≜')
  , ("to", '→')
  , ("gl", 'λ')
  , ("gm", 'μ')
  , ("gf", 'φ')
  , ("gn", 'ν')
  , ("gc", 'ψ')
  ]
