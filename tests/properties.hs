
-- | Test all properties automatically.

module Main where

import Test.Framework

import QuickCheck.Point   (testgroup_point)



main :: IO ()
main = defaultMain [testgroup_point]

