module Tui.Interaction
  -- Packages
  ( load_package
  , set_package
  , add_package_import

  -- Modules
  , load_file
  , add_import

  -- Terms
  , eval_text
  , query_text
  ) where

import Prelude hiding (mod, getLine, putStr, putStrLn, readFile, null)

import qualified Control.Exception as Exception
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Except (MonadError)
import Control.Monad.State (get)
import Data.Text (Text, unpack)
import Data.Text.IO (readFile)
import Data.List.NonEmpty (NonEmpty(..))
import Lens.Micro
import Lens.Micro.Mtl
import System.IO.Error (isDoesNotExistError)

import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec hiding (parse, runParser)
import Text.Megaparsec.Char as C
import Prettyprinter
import Prettyprinter.Render.Sigil
import qualified Brick.Types as T

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Interpret.Interpreter
import Sigil.Parse.Lexer

import InterpretUtils
import qualified Actions.Package as Package
import Tui.Types

eval_text :: forall m env s id. (MonadError SigilDoc m, MonadGen m)
  => Interpreter m SigilDoc env s -> (InteractiveState s -> Text) -> T.EventM id (InteractiveState s) ()
eval_text interpreter getText = do
  istate <- use interpreterState
  this <- get
  (pname, _, imports) <- use location
  (result, state') <- liftIO $ (run interpreter) istate (eval_expr interpreter pname imports (getText this))
  interpreterState .= state'
  case result of
    Right (val, ty) -> do
      outputState .= (show $ vsep [ "val:" <+> nest 2 (pretty val)
                                 , "type:" <+> nest 2 (pretty ty) ])
    Left err -> outputState .= show err

query_text :: forall m env s id. (MonadError SigilDoc m, MonadGen m) =>
                    Interpreter m SigilDoc env s
          -> (InteractiveState s -> Text) -> T.EventM id (InteractiveState s) ()
query_text interpreter getText = do
  istate <- use interpreterState
  this <- get
  (pname, _, imports) <- use location
  (result, state') <- liftIO $ (run interpreter) istate (eval_formula interpreter pname imports (getText this))
  interpreterState .= state'
  case result of
    Right subst -> do
      outputState .= (show $ vsep ["Solved with:", indent 2 (pretty subst)])
    Left err -> outputState .= show err

load_file :: forall m env s id. (MonadError SigilDoc m, MonadGen m)
  => Interpreter m SigilDoc env s -> T.EventM id (InteractiveState s) ()
load_file interpreter = do
  focus .= Palette
  paletteAction .= (\filename -> do
    istate <- use interpreterState
    pkg_name <- use (location._1)
    out <- liftIO $ (Right <$> readFile (unpack filename)) `Exception.catch` (pure . Left)
    case out of 
      Right text -> do
        (result, istate') <- liftIO $ (run interpreter) istate $ do
          mod <- eval_mod interpreter pkg_name filename text
          (intern_module interpreter) (mod^.module_header) mod
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
              Right val -> outputState .= "Success" >> availableModules .= val
      Left e
        | isDoesNotExistError e -> outputState .= ("file does not exist: " <> unpack filename)
        | otherwise -> outputState .= "IO error encountered reading file: " <> unpack filename)
                                     
    
add_import :: T.EventM id (InteractiveState s) ()
add_import = do
  focus .= Palette
  paletteAction .= (\import_statement -> do
    case Megaparsec.runParser pImport "import" import_statement of
      Left _ -> outputState .= "import parser failure"
      Right val -> outputState .= "Success" >> (location._3) %= (val :))

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
    (x:xs) -> pure (x:|xs)
  modifier <- pModifier <|> pure ImSingleton
  pure $ Im (path, modifier)

pModifier :: TParser ImportModifier
pModifier = 
  const ImWildcard <$> (lexeme (C.char '.') *> symbol "(…)")


add_package_import :: forall m env s id.
  Interpreter m SigilDoc env s -> T.EventM id (InteractiveState s) ()
add_package_import interp = do
  focus .= Palette
  paletteAction .= (\import_statement -> do
    let notWhitespace ' ' = False
        notWhitespace '\n' = False
        notWhitespace '\t' = False
        notWhitespace _ = True
    if all notWhitespace (unpack import_statement)
    then do
      -- TODO: We need to recheck the package with the new import
      packageImports %= (import_statement :)
      is <- use packageImports
      st <- use interpreterState
      pkg <- use $ location._1
      (_, st') <- liftIO $ (run interp) (st) (set_package_imports interp pkg is)
      interpreterState .= st'
      outputState .= "Success"

    else outputState .= "Package name must not contain whitespace")
  

load_package :: forall m env s id. (MonadError SigilDoc m, MonadGen m)
  => Interpreter m SigilDoc env s -> T.EventM id (InteractiveState s) ()
load_package interpreter = do
  focus .= Palette
  paletteAction .= (\filename -> do
    istate <- use interpreterState
    out <- liftIO $ Package.load_package interpreter istate filename 
    case out of 
      Right istate' -> do
        (mpkgs, istate'') <- liftIO $ (run interpreter) istate' (get_available_packages interpreter)
        interpreterState .= istate''
        case mpkgs of
          Right pkgs -> outputState .= "Success" >> loadedPackages .= pkgs
          Left err -> outputState .= show err
      Left err -> outputState .= show err)

set_package :: forall m env s id. 
  Interpreter m SigilDoc env s -> Text -> T.EventM id (InteractiveState s) ()
set_package interpreter pkg_name = do
  -- (possibly replace location with (Package, Either Module Imports)
  -- Location _1 = Package, _2 = Module, _3 = Imports 
  location._1 .= pkg_name
  location._2 .= Nothing
  moduleIx .= 0
  
  istate <- use interpreterState
  (mmodules, istate') <- liftIO $ (run interpreter) istate (get_available_modules interpreter pkg_name)
  interpreterState .= istate'
  case mmodules of 
    Right modules -> do 
      availableModules .= modules

    Left err -> do
      outputState .= show err
      availableModules .= []

  
  
