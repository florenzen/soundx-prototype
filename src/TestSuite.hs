module TestSuite where

import Test.HUnit

import qualified TestSimpleTypes as ST
import qualified TestSystemF as SF


testSuite =
    TestList [
      ST.testSuite,
      SF.testSuite
    ]

runTestSuite = runTestTT testSuite
