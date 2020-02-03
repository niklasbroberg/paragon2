-----------------------------------------------------------------------------
-- |
-- Module      :  TestAll
-- Copyright   :  (c) Bart van Delft 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Bart van Delft, vandeba@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module runs the various tests for the flow locks framework.
--
-----------------------------------------------------------------------------
--module TestAll where

import System.Exit (exitFailure)

import Test.QuickCheck (quickCheckResult)
import Test.QuickCheck.Test (isSuccess)
import Control.Monad (unless)

import Datalog (datalogTests)

-- | Runs the test suite for the replay library
main :: IO ()
main = do
  result <- mapM quickCheckResult 
            [datalogTests]
  unless (and $ map isSuccess result) exitFailure

