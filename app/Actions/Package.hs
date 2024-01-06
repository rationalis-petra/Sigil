module Actions.Package
  ( BuildDef(..)
  , build_def
  , b_package_name
  , b_export_modules
  , b_package_directories
  , build_dependency_list
  , load_package
  ) where


{------------------------------- PACKAGE ACTIONS -------------------------------}
{- Actions for dealing with packages and builds: A package file describes both -}
{- a package and the location (on disc) of its' modules. Therefore, we need to -}
{- be able to:                                                                 -}
{- • Parse package files                                                       -}
{- • Construct a dependency graph on (involves reading module headers via IO)  -}
{-   This dependency graph can then be used to load modules in-order.          -}
{-------------------------------------------------------------------------------}

import Prelude hiding (readFile)

import qualified Control.Exception as Exception
import Control.Monad.IO.Class (liftIO)
import Control.Monad (void, join, forM)
import Control.Monad.Except (MonadError, ExceptT, runExceptT, throwError)
import Control.Lens (makeLenses, (^.))
import Data.Text (Text, unpack, pack)
import Data.Text.IO (readFile)
import Data.Either (lefts)
import Data.List (intersperse, isSuffixOf)
import Data.List.NonEmpty (toList)
import Data.Foldable (fold)
import qualified Data.Map as Map
import qualified Data.Set as Set

import System.IO.Error (isDoesNotExistError)
import System.Directory
  
import Topograph
import Prettyprinter
import Prettyprinter.Render.Sigil
import Text.Megaparsec (runParser, takeWhile1P, mkPos, errorBundlePretty)
import qualified Text.Megaparsec.Char.Lexer as L

import Sigil.Parse ()
import Sigil.Parse.Outer (mod_header)
import Sigil.Parse.Combinator
import Sigil.Parse.Lexer
import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Interpret.Interpreter
import Sigil.Concrete.Internal (InternalCore)

import InterpretUtils

data BuildDef = BuildDef
  { _b_package_name :: Text
  , _b_export_modules :: [Text]
  , _b_import_packages :: [Text]
  , _b_package_directories :: [Text]
  }

$(makeLenses ''BuildDef)

build_def :: ParserT m BuildDef
build_def = do
  L.nonIndented scn package
  where
    package = do
      symbol "package"
      name <- anyvar
      scn
      void $ L.indentGuard scn GT (mkPos 1)
      provs <- L.indentBlock scn provides
      reqs <- L.indentBlock scn requires <||> pure []
      dirs <- L.indentBlock scn directories
      pure $ BuildDef name provs reqs dirs 

    provides = do 
      symbol "provide"
      pure $ L.IndentMany Nothing pure anyvar 

    requires = do 
      symbol "require"
      pure $ L.IndentMany Nothing pure anyvar 

    directories = do 
      symbol "directories"
      pure $ L.IndentMany Nothing pure dirName 

    dirName = lexeme $ takeWhile1P (Just "directory-character") (/= '\n')
    
  
  
build_dependency_list :: [FilePath] -> IO (Either SigilDoc [FilePath])
build_dependency_list dirnames = do
  -- Step 1: Collate all files (*.sl) in the directories
  -- TODO: what if symlinks result in loop structures?
  let rec_paths :: [FilePath] -> [FilePath] -> IO [FilePath]
      rec_paths [] files = pure files
      rec_paths unexplored files = do
        entries <- forM unexplored $ \path -> do
          vals <- listDirectory path
          pure $ map (mappend path . (:) '/' ) vals
        tagged_entries <- mapM (\e -> (,) <$> doesDirectoryExist e <*> pure e) (join entries)
        let dirs   = fmap snd . filter fst $ tagged_entries
            files' = fmap snd . filter (\v -> (".sl" `isSuffixOf` snd v) && not (fst v)) $ tagged_entries
        rec_paths dirs (files <> files')

  files <- rec_paths dirnames []

  -- Step 2: Read the headers of all these files and convert these headers into
  --         a Map-representation of a DAG 
  graph_map <- runExceptT $ forM files $ \filename -> do
    contents <- liftIO $ readFile filename
    case runParser mod_header filename contents of 
      Left err -> throwError $ pretty $ errorBundlePretty err
      Right (_, ports) ->
        pure (filename, Set.fromList $ map (unpack . fold . intersperse "/" . toList . unPath . fst . unImport) (lefts ports))

  -- Step 4: Use Topograph to sort the graph (or return an error)
  case graph_map of
    Right graph ->
      case runG (Map.fromList graph) $ \G{..} -> fmap gFromVertex gVertices of 
        Right val -> pure $ Right val
        Left _ -> pure $ Left "cycle"
    Left err -> pure $ Left err


load_package_files :: forall m e s t f. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
                    Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f
                   -> s -> Text -> [String] -> IO (Either SigilDoc s)
load_package_files interpreter istate pkg_name files = runExceptT (go istate files) 
  where
     -- TODO: probably can't as easily rewind state when using non-haskell backend...
    go :: s -> [String] -> ExceptT SigilDoc IO s
    go istate (filename:files) = do
      out <- liftIO $ (Right <$> readFile filename)
        `Exception.catch` (\case
                              e | isDoesNotExistError e -> pure $ Left $ pretty ("file does not exist: " <> filename)
                                | otherwise -> pure $ Left $ pretty ("IO error encountered reading file: " <> filename))
      contents <- case out of 
        Right val -> pure val
        Left err -> throwError err
      (result, istate') <- liftIO $ (run interpreter) istate $ do
        mod <- eval_mod interpreter pkg_name (pack filename) contents
        (intern_module interpreter) pkg_name (mod^.module_header) mod
        pure mod
      case result of
        Left err -> throwError err
        _ -> go istate' files

    go istate [] = pure istate


-- build_dependency_list :: [FilePath] -> IO (Either SigilDoc [FilePath])
load_package :: forall m e s t f. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
                    Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f
          -> s -> Text -> IO (Either SigilDoc s)
load_package interp state filename = do
    out <- liftIO $ (Right <$> readFile (unpack filename)) `Exception.catch` (pure . Left)
    case out of 
      Right contents -> do
        case runParser build_def (unpack filename) contents of 
          Right bdef -> do
            let
              split out acc = \case 
                [] -> reverse (reverse acc : out)
                ('/' : str) -> split (reverse acc : out) [] str
                (c : str) -> split out (c:acc) str
              path_modifier = fold . (\v -> zipWith (<>) v (repeat "/")) . reverse . drop 1 . reverse $ split [] [] (unpack filename)
            edlist <- liftIO $ build_dependency_list (fmap (mappend path_modifier . unpack) (bdef^.b_package_directories))
            case edlist of 
              Right dlist -> do
                (merr, state') <- liftIO $ (run interp) state $ do
                  (intern_package interp)
                    (bdef^.b_package_name) (Package
                                  (PackageHeader (bdef^.b_package_name) (bdef^.b_export_modules) (bdef^.b_import_packages))
                                  (MTree Map.empty))
                case merr of 
                  Right () -> liftIO $ load_package_files interp state' (bdef^.b_package_name) dlist
                  Left err -> pure $ Left err
              Left err -> pure $ Left err
          Left err -> pure $ Left $ pretty $ errorBundlePretty err
      Left e
        | isDoesNotExistError e -> pure $ Left $ "file does not exist: " <> pretty filename
        | otherwise -> pure $ Left $ "IO error encountered reading file: " <> pretty filename
