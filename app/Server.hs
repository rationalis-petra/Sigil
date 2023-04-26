module Server
  ( ServerOpts(..)
  , server) where


import Prelude hiding (putStrLn)
import Control.Monad (forever)
import Control.Monad.Except (ExceptT, runExceptT, catchError, throwError)
import qualified Control.Exception as Ex
import Control.Concurrent (forkFinally)
  
import Data.Bifunctor
import qualified Data.Map as Map
import qualified Data.ByteString as Bs
import qualified Data.Set as Set
import Text.Megaparsec hiding (runParser)
import Data.Text.IO
import Data.Text (Text, pack)

import Data.Aeson (encode)
import Data.Aeson.Types hiding (Parser)
import Pipes
import Pipes.Parse
import qualified Pipes.Aeson as AP
import Pipes.Aeson (DecodingError)
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import Prettyprinter
import Prettyprinter.Render.Glyph
import Prettyprinter.Render.Text

import Glyph.Abstract.Environment hiding (bind)
import Glyph.Concrete.Typed
import Glyph.Parse.Mixfix
import Glyph.Parse
import Glyph.Analysis.NameResolution
import Glyph.Analysis.Typecheck
import Glyph.Interpret.Term


data ServerOpts = ServerOpts
  { port :: Int
  }
  deriving (Show, Read, Eq)

default_precs :: Precedences
default_precs = Precedences
  (Map.fromList
   [ ("sum"  , PrecedenceNode Set.empty (Set.fromList ["prod"]))
   , ("prod" , PrecedenceNode Set.empty (Set.fromList ["ppd"]))
   , ("ppd"  , PrecedenceNode Set.empty (Set.fromList ["tight"]))
   , ("ctrl" , PrecedenceNode Set.empty (Set.fromList ["tight"]))
   , ("tight", PrecedenceNode Set.empty (Set.fromList ["tight"]))
   , ("tight", PrecedenceNode Set.empty (Set.fromList ["close"]))
   , ("close", PrecedenceNode Set.empty Set.empty)
   ])
  "sum" "ppd" "ppd" "close"

server :: ServerOpts -> IO ()
server opts = do
  runTCPServer Nothing (show $ port opts) threadWorker

-- start a server which listens for incoming bytestrings
-- from the "network-run" package.
runTCPServer :: Maybe HostName -> ServiceName -> (Socket -> IO a) -> IO a
runTCPServer mhost port threadWorker = withSocketsDo $ do
    addr <- resolve
    Ex.bracket (open addr) close loop
  where
    resolve = do
        let hints = defaultHints {
                addrFlags = [AI_PASSIVE]
              , addrSocketType = Stream}
        head <$> getAddrInfo (Just hints) mhost (Just port)
    open addr = Ex.bracketOnError (openSocket addr) close $ \sock -> do
        setSocketOption sock ReuseAddr 1
        withFdSocket sock setCloseOnExecIfNeeded
        bind sock $ addrAddress addr
        listen sock 2
        return sock
    loop sock = forever $ Ex.bracketOnError (accept sock) (close . fst)
        $ \(conn, _peer) -> void $
            -- 'forkFinally' alone is unlikely to fail thus leaking @conn@,
            -- but 'E.bracketOnError' above will be necessary if some
            -- non-atomic setups (e.g. spawning a subprocess to handle
            -- @conn@) before proper cleanup of @conn@ is your case
            forkFinally (threadWorker conn) (const $ gracefulClose conn 5000)

threadWorker :: Socket -> IO ()  
threadWorker socket = go (packetProducer socket)
  where
    go :: Producer Bs.ByteString IO () -> IO ()  
    go p = do
      (mmessage, cont) <- runStateT messageParser p
      case mmessage of 
        Just message -> do
          procErr message 
          go cont
        Nothing -> pure ()
        
    procErr :: Either DecodingError InMessage -> IO () 
    procErr = either id id .  bimap (putStrLn . ("Error: " <>) . pack . show) (processMessage socket)  


processMessage :: Socket -> InMessage -> IO ()  
processMessage socket = \case
  RunCode uid _ code ->
    let object = case eval_term code of
          Right (val, _) -> toJSON $ OutResult uid (renderStrict (layoutPretty defaultLayoutOptions (pretty val)))
          Left err -> toJSON $ OutError uid (renderStrict (layoutPretty defaultLayoutOptions err))
    in do
      putStrLn $ "sending" <> (pack $ show $ encode object)
      sendAll socket (Bs.toStrict $ encode $ object)
      sendAll socket "\n"
   

  where 
    eval_term :: Text -> Either GlyphDoc (TypedCore, TypedCore)
    eval_term line = run_gen $ runExceptT $ meval line

    meval :: Text -> ExceptT GlyphDoc Gen (TypedCore, TypedCore)
    meval line = do
      parsed <- parseToErr (core default_precs <* eof) "console-in" line 
      resolved <- resolve parsed
        `catchError` (throwError . (<+>) "resolution:")
      (term, ty) <- infer (env_empty :: Env (Maybe TypedCore, TypedCore)) resolved
        `catchError` (throwError . (<+>) "inference:")
      norm <- normalize (env_empty :: Env (Maybe TypedCore, TypedCore)) ty term
        `catchError` (throwError . (<+>) "normalization:")
      pure $ (norm, ty)

packetProducer :: MonadIO m => Socket -> Producer Bs.ByteString m ()
packetProducer socket = do
  msg <- lift . liftIO $ recv socket 4096
  yield msg
  packetProducer socket

messageParser :: Monad m => Parser Bs.ByteString m (Maybe (Either DecodingError InMessage))
messageParser = AP.decode

  
data InMessage
  = RunCode Int [Text] Text

data OutMessage
  = OutResult Int Text
  | OutError Int Text
  

instance FromJSON InMessage where   
  parseJSON (Object v) = do 
    tipe <- v .: "type"
    case tipe of 
      "RunCode" -> RunCode
        <$> v .: "uid"
        <*> v .: "path"
        <*> v .: "code"
      _ -> fail ("unexpected type " <> tipe)
  parseJSON invalid = typeMismatch "In Message" invalid

instance ToJSON OutMessage where 
  toJSON (OutResult uid val) = 
    object [ ("type", toJSON ("Result" :: Text))
           , ("uid", toJSON uid)
           , ("val", toJSON val)
           ]

  toJSON (OutError uid msg) = 
    object [ ("type", toJSON ("Error" :: Text))
           , ("uid", toJSON uid) 
           , ("msg", toJSON msg)
           ] 
