module Server
  ( ServerOpts(..)
  , server) where


import Prelude hiding (putStrLn)
import Control.Monad (forever)
import Control.Monad.Except (MonadError)
import qualified Control.Exception as Ex
import Control.Concurrent (forkFinally)
  
import Data.Bifunctor
import qualified Data.ByteString as Bs
import Data.Text.IO
import Data.Text (pack)

import Data.Aeson (encode)
import Data.Aeson.Types hiding (Parser)
import Pipes
import Pipes.Parse
import qualified Pipes.Aeson as AP
import Pipes.Aeson (DecodingError)
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import Prettyprinter
import Prettyprinter.Render.Sigil
import Prettyprinter.Render.Text

import Sigil.Abstract.Names hiding (bind)
import Sigil.Abstract.Environment
import Sigil.Concrete.Internal
import Sigil.Interpret.Interpreter

import Server.Agent
import InterpretUtils


data ServerOpts = ServerOpts
  { port :: Int
  }
  deriving (Show, Read, Eq)


server :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> ServerOpts -> IO ()
server interpreter opts = do
  putStrLn "starting server!"
  runTCPServer Nothing (show $ port opts) (threadWorker interpreter)

-- start a server which listens for incoming bytestrings
-- from the "network-run" package.

runTCPServer :: Maybe HostName -> ServiceName -> (Socket -> IO a) -> IO a
runTCPServer mhost port worker = withSocketsDo $ do
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
            forkFinally (worker conn) (const $ gracefulClose conn 5000)


threadWorker :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e)
  => Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> Socket -> IO ()
threadWorker interpreter socket = putStrLn "worker started!" >> loop (packetProducer socket) (start_state interpreter)
  where
    loop :: Producer Bs.ByteString IO () -> s -> IO ()
    loop p state = do
      (mmessage, cont) <- runStateT messageParser p
      case mmessage of 
        Just message -> do
          state' <- procErr state message
          loop cont state' 
        Nothing -> do
          _ <- run interpreter state $ stop interpreter
          pure ()
        
    procErr :: s -> Either DecodingError InMessage -> IO s
    procErr state
      = either (>> pure state) id .  bimap (putStrLn . ("Error: " <>) . pack . show) (processMessage interpreter state socket)


processMessage :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e)
  => Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> s -> Socket -> InMessage -> IO s
processMessage interp@(Interpreter {..}) state socket = \case
  EvalExpr uid _ code -> do
    (result, state') <- run state $ eval_expr interp [] code
    let object = case result of
          Right (val, _) -> toJSON $ OutResult uid (renderStrict (layoutPretty defaultLayoutOptions (pretty val)))
          Left err -> toJSON $ OutError uid (renderStrict (layoutPretty defaultLayoutOptions err))
    sendAll socket (Bs.toStrict $ encode object)
    putDocLn (either id (pretty . fst) result)
    sendAll socket "\n"
    pure state'

packetProducer :: MonadIO m => Socket -> Producer Bs.ByteString m ()
packetProducer socket = do
  msg <- lift . liftIO $ recv socket 4096
  yield msg
  packetProducer socket

messageParser :: Monad m => Parser Bs.ByteString m (Maybe (Either DecodingError InMessage))
messageParser = AP.decode

  

