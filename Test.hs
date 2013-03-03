
module Main where

import Control.DeepSeq

import ADP.Fusion (test)

main = do
  l <- getLine
  print l
  let rl = read l :: Int
--  mapM_ test [0 .. rl]
  x <- (l,rl) `deepseq` test rl
  return ()
--  print x

