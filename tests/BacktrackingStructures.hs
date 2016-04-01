
{-# Language MagicHash #-}

module Main where

import           Criterion.Main
import           Data.Vector.Fusion.Stream.Monadic (Stream,foldl',mapM_)
import           Data.Vector.Fusion.Util
import           Data.Vector.Unboxed (Vector, fromList)
import           GHC.Exts (inline, Int(..), (<=#) )
import           Prelude hiding (mapM_)
import           System.IO.Unsafe
import qualified Data.FMList as F



listLeft :: Int -> Int
listLeft k = sum $ go k []
  where go 0 xs = xs
        go k xs = go (k-1) (k:xs)
{-# NoInline listLeft #-}

listRight :: Int -> Int
listRight k = sum $ go k []
  where go 0 xs = xs
        go k xs = go (k-1) (xs++[k])
{-# NoInline listRight #-}

listRightRev :: Int -> Int
listRightRev k = sum . reverse $ go k []
  where go 0 xs = xs
        go k xs = go (k-1) (k:xs)
{-# NoInline listRightRev #-}

listBoth :: Int -> Int
listBoth k = sum $ go (k `div` 2) []
  where go 0 xs = xs
        go k xs = go (k-1) (k:xs++[k])
{-# NoInline listBoth #-}

fmLeft :: Int -> Int
fmLeft k = sum . F.toList $ go k F.empty
  where go 0 xs = xs
        go k xs = go (k-1) (k `F.cons` xs)
{-# NoInline fmLeft #-}

fmRight :: Int -> Int
fmRight k = sum . F.toList $ go k F.empty
  where go 0 xs = xs
        go k xs = go (k-1) (xs `F.snoc` k)
{-# NoInline fmRight #-}

-- |

benchWithK s k =
  bgroup s
    [ bench "listLeft"      $ whnf listLeft  k
    , bench "listRight"     $ whnf listRight k
    , bench "listRightRev"  $ whnf listRight k
    , bench "listBoth"      $ whnf listBoth  k
    , bench "fmLeft"        $ whnf fmLeft    k
    , bench "fmRight"       $ whnf fmRight   k
    ]
{-# Inline benchWithK #-}

-- |

main :: IO ()
main = do
  defaultMain
    [ benchWithK "10"      10
    , benchWithK "20"      20
    , benchWithK "100"    100
    , benchWithK "1000"  1000
    ]

