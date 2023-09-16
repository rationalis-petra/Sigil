module Sigil.Parse.Memoised () where

{------------------------- MEMOISING PARSER COMBINATOR -------------------------}
{-                                                                             -}      
{- Unfortunately, the mixfix parsing algorithm used in Mixfix.hs can require   -}      
{- large amounts of backtracking. To combat this, we user a memoising parser   -}      
{- combinator.                                                                 -}      
{-                                                                             -}      
{- The implementation provided here is based on the paper 'Memoisation in      -}      
{- Top-down Parsing' by Mark Johnson.                                          -}      
{-                                                                             -}      
{-                                                                             -}      
{-                                                                             -}      
{-                                                                             -}      
{-                                                                             -}      
{-                                                                             -}      
{-------------------------------------------------------------------------------}      
