
-- | Test all properties automatically. We keep the QC2 modules in the main
-- library for now, as this allows for more efficient repl tests.

module Main where

import Test.Framework.Providers.QuickCheck2
import Test.Framework.TH

import qualified ADP.Fusion.QuickCheck.Subword  as QSW
import qualified ADP.Fusion.QuickCheck.Set      as QS
import qualified ADP.Fusion.QuickCheck.Point    as QP


prop_sv_OII = QSW.prop_sv_OII

main :: IO ()
main = $(defaultMainGenerator)

