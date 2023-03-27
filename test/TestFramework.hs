module TestFramework (
  TestGroup(..),
  Test(..)) where

{--------------------------------- TEST TYPES ----------------------------------}
{- This file contains types and utilities for building test-suites. By making  -}
{- specific types for the tests, it becomes easier to do the following:        -}
{- • Enable/disable specific tests or groups of tests via the command line     -}
{- • Report exactly when/where errors occur                                    -}
{- • Alter verbosity levels for the output                                     -}
{- • etc.                                                                      -}
{-                                                                             -}
{- Tests are arranged into a tree, with nodes being specific groupings of      -}
{- tests, and leaves being individual tests. Each node has a string identifier -}
{- but leaves do not. Tests can optionally provide a Doc (prettyprinter) error -}
{- message.                                                                    -}
{-------------------------------------------------------------------------------}

import Data.Text
import Prettyprinter

data TestGroup ann =
  TestGroup { _group_name :: Text, _children :: Either [TestGroup ann] [Test ann] }

data Test ann = Test { _test_name :: Text, _result :: Maybe (Doc ann) }
