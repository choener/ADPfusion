
-- | Test all properties automatically. We keep the QC2 modules in the main
-- library for now, as this allows for more efficient repl tests.

module Main where

--import Test.Framework.Providers.QuickCheck2
--import Test.Framework.TH
import Test.Framework

import QuickCheck.Point   (testgroup_point)
import QuickCheck.Set     (testgroup_set)



main :: IO ()
main = defaultMain [testgroup_point, testgroup_set]

