module Glyph.Agent
  ( module Glyph.Agent.Agent ) where

{------------------------------------ AGENT ------------------------------------}
{- The Agent System is used by all main modes of interaction (server, compiler,-}
{- interpreter). The Agent system essentially manages the contexts in which    -}
{- other modules (parser, type checking etc.) operate, i.e. loaded libraries   -}
{- etc.                                                                        -}
{-                                                                             -}
{- It is a parallel system which can have multiple running processes sharing   -}
{- some resources (e.g. the standard library modules) while, e.g. using        -}
{- different versions of a loaded module.                                      -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Glyph.Agent.Agent
