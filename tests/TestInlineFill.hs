
{-# Language MagicHash #-}

module Main where

import Criterion.Main
import Data.Vector.Fusion.Stream.Monadic (Stream,foldl',mapM_)
import Data.Vector.Fusion.Util
import Data.Vector.Unboxed (Vector, fromList)
import GHC.Exts (inline, Int(..), (<=#) )
import Prelude hiding (mapM_)
import System.IO.Unsafe

import Data.PrimitiveArray hiding (fromList)

import ADP.Fusion.Point



-- |

data Simple m x r c = Simple
  { nil :: () -> x
  , unp :: x -> c -> x
  , h   :: Stream m x -> m r
  }

-- |

simple :: (Monad m) => Simple m Int Int Int
simple = Simple
  { nil = \ () -> 0
  , unp = \ x c -> x + c
  , h = foldl' max' 0
  }
{-# Inline simple #-}

-- |

max' :: Int -> Int -> Int
max' (I# l) (I# r) =
  case l <=# r of
    0# -> I# l
    1# -> I# r
{-# Inline max' #-}

-- |

grammar Simple{..} !c !(ILol a b l d) =
  let t = ITbl a b l d ( nil <<< Epsilon |||
                         unp <<< t % c   ... h
                       )
  in Z:.t

-- | Measure table filling only. We hand over the table to be filled and
-- the terminal data.
--
-- This is "dangerous" because we violate purity.

forwardDefault :: Vector Int -> Unboxed (PointL I) Int -> Int
forwardDefault !cs !t = unId $ axiom u
  where (Z:.u) = mutateTablesDefault
               $ grammar simple
                   (chr cs)
                   (ILol 0 0 EmptyOk t)
               :: Z :. T
{-# NoInline forwardDefault #-}

-- |

forwardNew :: Vector Int -> Unboxed (PointL I) Int -> Int
forwardNew !cs !t = unId $ axiom u
  where (Z:.u) = mutateNew
               $ grammar simple
                   (chr cs)
                   (ILol 0 0 EmptyOk t)
               :: Z :. T
{-# NoInline forwardNew #-}

-- |

mutateNew :: Z:.T -> Z:.T
mutateNew (Z:.ITbl bo lo uuu arr f) = Z:.ITbl bo lo uuu arr' f where
  (from,to) = bounds arr
  arr' = unsafePerformIO $ do
            marr <- unsafeThaw arr
            flip mapM_ (streamUp from to) $ \k -> do
              !z <- (return . unId) $ inline $ f to k
              writeM marr k z
            return arr
{-# Inline [0] mutateNew #-}

-- | Type of tables.

type T = ITbl Id Unboxed EmptyOk (PointL I) Int

-- |

main :: IO ()
main = do
  let !from = 0
  let !to   = 1000000
  let !cs = fromList [from + 1 .. to]
      !t  = fromAssocs (pointLI from) (pointLI to) (-999999) []
  let !s1 = forwardNew cs t
  let !rr = forwardDefault cs t
  let !s2 = forwardNew cs t
  print rr
  print (s1,s2)
  defaultMain
    [ bench "default" $ whnf (forwardDefault cs) t
    , bench "new    " $ whnf (forwardNew     cs) t
    ]

