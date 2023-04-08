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
{-                                                                             -}
{- This test module is still a work in progress, with plas to add the          -}
{- following features:                                                         -}
{- • Dependencies: If one test assumed functions tested by another module work -}
{-   properly, then this can be explicitly defined.                            -}
{- • Run tests in parallel (particularly as the test-suite grows)              -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Data.Text
import Prettyprinter
import Prettyprinter.Render.Glyph

data TestGroup =
  TestGroup { _group_name :: Text, _children :: Either [TestGroup] [Test] }

data Test = Test { _test_name :: Text, _result :: Maybe (Doc GlyphStyle) }
