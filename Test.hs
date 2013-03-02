
module Main where

import ADP.Fusion (test)

main = do
  l <- getLine
  print l
  x <- test (read l * 1)
  print x
