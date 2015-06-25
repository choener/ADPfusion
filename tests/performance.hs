
module Main where

import           Data.Vector.Fusion.Util
import           GHC.Stats
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Mem
import           System.Environment
import           GHC.Conc (pseq)
import           GHC.Generics
import qualified Data.Vector as V
import           Control.Arrow (second)
import           Data.Int(Int64)
import           System.Exit

import           ADP.Fusion hiding (Split)
import           Data.PrimitiveArray hiding (map)
import           BenchmarkHistory



-- | All grammars require a signature.

data Split m x r = Split
  { nil :: ()  -> x
  , lef :: Int -> x -> x
  , spl :: x   -> x -> x
  , h   :: SM.Stream m x -> m r
  }

-- makeAlgebraProduct ''Split

algMax :: Monad m => Split m Int Int
algMax = Split
  { nil = \ () -> 0
  , lef = \k x -> k+x
  , spl = \ x y   -> x+y
  , h   = SM.foldl' max 0
  }
{-# Inline algMax #-}

gLeft Split{..} c t' =
  let t = t'  ( lef <<< chr c % t   |||
                spl <<< t % t       |||
                nil <<< Epsilon     ... h
              )
  in Z:.t
{-# Inline gLeft #-}

mkArrs :: Int -> (VU.Vector Int, Unboxed Subword Int)
mkArrs n = ( VU.enumFromTo 1 n
           , fromAssocs (subword 0 0) (subword 0 n) (-999999) []
           )
{-# NoInline mkArrs #-}

-- | WARNING: Multiple runs of @runLeft@ make use of the same @arr@. This
-- is, of course, dangerous. Unless you know what you are doing.

runLeft :: (VU.Vector Int, Unboxed Subword Int) -> Int -> Int
runLeft (!i, !arr) k = seq k d where
--  i   = VU.enumFromTo 1 k
  n   = VU.length i
--  arr = fromAssocs (subword 0 0) (subword 0 n) (-999999) []
  (Z:.t) = runLeftForward i arr
  d = unId $ axiom t
{-# NoInline runLeft #-}

runLeftForward :: VU.Vector Int -> Unboxed Subword Int -> Z:.ITbl Id Unboxed Subword Int
runLeftForward !i !arr = mutateTablesDefault
               $ gLeft algMax
                   i
                   (ITbl 0 0 EmptyOk arr)
{-# NoInline runLeftForward #-}



main :: IO ()
main = do
  es <- sequence
    [ benchmark 10000 ("bench-0100.csv") mkArrs runLeft  100
    , benchmark    10 ("bench-1000.csv") mkArrs runLeft 1000
    , benchmark     1 ("bench-2000.csv") mkArrs runLeft 2000
    ]
  let ok = all (== ExitSuccess) es
  if ok
    then exitSuccess
    else exitFailure

