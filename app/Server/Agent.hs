module Server.Agent (InMessage(..), OutMessage(..)) where


{---------------------------- CANONICAL INTERPRETER ----------------------------}
{- This file contains the definition for the 'canonical' interpreter. It is    -}
{- a simple tree-walking interpreter whose behaviour should serve as a         -}
{- reference point to other interpreters. It is also a fall-back interpreter,  -}
{- Guaranteed to run on any platform, and so is useful if, the libraries       -}
{- needed to run the other interpreters (e.g. JVM) aren't available on the     -}
{- current machine.                                                            -}
{-------------------------------------------------------------------------------}

import Data.Text (Text)
import Data.Aeson.Types hiding (Parser)

-- data AgentState = AgentState m
--   { current_interpreter :: m. Interpreter m
--     current_interpreter_monad :: m ()

-- data AgentState = AgentState m
--   { current_interpreter :: m. Interpreter m
--   , current_interpreter_monad :: m ()
--   , available_backends :: [ ]
--   }

data InMessage
  = EvalExpr Int [Text] Text
  deriving (Eq, Show)
  -- | LoadModule Int [Text] Text

data OutMessage
  = OutResult Int Text
  | OutError Int Text
  deriving (Eq, Show)

-- doMessage :: InMessage -> AgentState -> IO (OutMessage, AgentState)

-- switch_interpreter :: AgentState -> IO (Message, AgentState)

-- eval_code :: Text -> [Text] -> AgentState -> IO (Message, AgentState)

-- load_module :: Text -> [Text] -> AgentState -> IO (Message, AgentState)

-- load_module_part :: Text -> [Text] -> AgentState -> IO (Message, AgentState)

-- switch_backend :: AgentState -> IO (Message, AgentState)


instance FromJSON InMessage where   
  parseJSON (Object v) = do 
    tipe <- v .: "type"
    case tipe of 
      "EvalExpr" -> EvalExpr
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
