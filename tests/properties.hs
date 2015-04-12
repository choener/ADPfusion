
module Main where

import Test.Framework.Providers.QuickCheck2
import Test.Framework.TH

import qualified ADP.Fusion.QuickCheck.Subword as QS


prop_sv_OII = QS.prop_sv_OII

main :: IO ()
main = $(defaultMainGenerator)

