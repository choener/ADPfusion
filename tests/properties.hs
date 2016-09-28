
-- | Test all properties automatically.

module Main where

import Test.Tasty

import QuickCheck.Point   (testgroup_point)



main :: IO ()
main = defaultMain testgroup_point

