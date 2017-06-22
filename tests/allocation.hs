
module Main where

import GHC.Stats
import Text.Printf
import System.Exit
import Data.Int
import System.Mem

import BenchmarkFun

rep :: Int -> (Int -> Int -> Int) -> Int
rep k f = go 0 k where
  go !z 0  = z
  go !z !k = go (z+y) (k-1)
    where y = f (k `rem` 140) 0
{-# NoInline rep #-}

main :: IO ()
main = do
  print $ rep 10000000 stream_Strng2_V
  performGC
  stats <- getGCStats
  let ba = bytesAllocated stats
  let maxAlloc = 480077128 :: Int64
  if ba >= maxAlloc
  then do
    printf "%d bytes allocated, expected <= %d\n!" ba maxAlloc
    exitFailure
  else do
    printf "total allocation is fine!\n"
    exitSuccess

