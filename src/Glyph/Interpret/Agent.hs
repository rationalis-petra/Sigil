module Glyph.Interpret.Agent
  ( Task(..)
  , TaskDesc(..)
  , World(..)
  , TaskInfo(..) ) where

-- import Control.Lens

{------------------------------------ DRAFT ------------------------------------}
{-                                                                             -}
{- Tasks & Queries                                                             -}
{- + Tasks will perform some modification to the environment, e.g.             -}
{-   reload a module, add a new definition, etc.                               -}
{- + Queries will not update the environment, e.g. evaluate an expression,     -}
{-   ask for documentation, etc.                                               -}
{- Upon creation, both return a unique handle which can be used to check       -}
{- their status, restart them, etc.                                            -}
{- As they have a UID, it's best that                                          -}
{-                                                                             -}
{- Versioning                                                                  -}
{- + We want tasks to run on a consistent 'version' of the context, i.e. if    -}
{-   we change the definition of `fact`, this should not affect a process      -}
{-   running which uses `fact` - it should still use the old version           -}
{- + However, we may want tasks to opt-in to live updates!                     -}
{-                                                                             -}
{- Agent State                                                                 -}
{- + A 'world' represents a tree of modules & current module path at a given   -}
{-   point in time. It represents a context in which a query or task is        -}
{-   evaluated. Multiple worlds may exist concurrently, if a task executes     -}
{-   before another task or query has finished.                                -}
{-------------------------------------------------------------------------------}


data Task = Task
  { _task_description :: TaskDesc
  , _task_id :: Int
  , _task_world :: World
  }
  
data TaskDesc = TaskDesc { _task_info :: TaskInfo, _world :: Maybe World }

data World = World ()  

data TaskInfo
  -- | LoadModule ModuleDesc 
  = AddDef ()

-- data QueryDesc
--   = Eval Term
--   | EvalIO Term

  

-- data Agent = Agent
--   { _current_world :: World
--   }

-- get_world :: Agent -> World

-- start_task :: Agent -> TaskDesc -> IO Task

-- task_status :: Agent -> Task -> IO (Either (Doc GlyphDoc) TaskResult)

-- start_query :: Agent -> QueryDesc -> IO Task

-- query_status :: Agent -> Query -> IO (Either (Doc GlyphDoc) TaskResult)
