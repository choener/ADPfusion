
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
  let rep_count = 10000000 :: Int64
  print $ rep (fromIntegral rep_count) stream_Strng2_V
  performGC
  stats <- getGCStats
  let ba = bytesAllocated stats
  -- allow exactly one @I# 0@ allocation each round
  -- including a tiny bit of additional overhead
  let maxAlloc = 32 * rep_count + 100000 :: Int64
  if ba >= maxAlloc
  then do
    printf "FAIL %d bytes allocated (%d allowed) [[%d / %d]]\n" (ba `div` rep_count) (maxAlloc `div` rep_count) ba maxAlloc
    exitFailure
  else do
    printf "SUCCESS %d bytes allocated (%d allowed) [[%d / %d]]\n" (ba `div` rep_count) (maxAlloc `div` rep_count) ba maxAlloc
    exitSuccess

