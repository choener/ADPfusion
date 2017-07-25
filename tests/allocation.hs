
module Main where

import GHC.Stats
import Text.Printf
import System.Exit
import Data.Int
import System.Mem

import BenchFun.Test2V_1
import BenchFun.Test2V_2

rep :: Int -> (Int -> Int -> Int) -> Int
rep k f = go 0 k where
  go !z 0  = z
  go !z !k = go (z+y) (k-1)
    where y = f (k `rem` 140) (k `rem` 140)
{-# Inline rep #-}

prettify :: (String, Int64, Int64, Int64, Int -> Int -> Int) -> IO Bool
prettify (funname, rep_count, allocmul, allocadd, f) = do
  performGC
  stats1 <- getGCStats
  let !ba1 = bytesAllocated stats1
  let !sec1 = wallSeconds stats1
  print $ rep (fromIntegral rep_count) f
  performGC
  stats2 <- getGCStats
  let !ba2 = bytesAllocated stats2
  let !sec2 = wallSeconds stats2
  let !ba = ba2 - ba1
  let !sec = sec2 - sec1
  -- allow exactly one @I# 0@ allocation each round
  -- including a tiny bit of additional overhead
  let maxAlloc = allocmul * rep_count + allocadd :: Int64
  let pf s = printf "%8s %15s %6d bytes allocated (%6d allowed) [[%10d / %10d]]   %8.5f seconds\n"
                    s funname ((ba - allocadd) `div` rep_count) ((maxAlloc - allocadd) `div` rep_count) ba maxAlloc sec
  if ba > maxAlloc
  then do
    pf "FAIL"
    return False
  else do
    pf "SUCCESS"
    return True
{-# NoInline prettify #-}


main :: IO ()
main = do
  runs <- mapM prettify
    [ ("Test2_V_1", 10^5, 129,  576, stream_Test2_V_1)
--    , ("Test2_V_2", 10^7,  48, 1800, stream_Test2_V_2)
    ]
  if (and runs) then exitSuccess else exitFailure

