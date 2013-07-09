{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

-- | This is not really a working example, but rather to check the GHC-Core for
-- fusion.

--module ADP.Fusion.Examples.TwoDim where
module Main where

import Data.Vector.Fusion.Stream.Monadic (Stream (..))
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector as V
import Data.Array.Repa.Index
import Control.Monad
import Control.Monad.Trans.Class
import qualified Control.Monad.Trans.Writer.Lazy as W
import qualified Control.Arrow as A
import System.IO.Unsafe (unsafePerformIO)
import Control.Applicative

import Data.Array.Repa.Index.Points
import Data.PrimitiveArray as PA
import Data.PrimitiveArray.Zero as PA

import ADP.Fusion hiding (empty)
import ADP.Fusion.Empty hiding (empty)
import ADP.Fusion.Chr
import ADP.Fusion.Table
import ADP.Fusion.Multi
import Data.Array.Repa.Index.Subword
import ADP.Fusion.TH



main = do
  ls <- lines <$> getContents
  align ls

align [] = return ()
align [c] = error "single last line"
align (a:b:xs) = do
  putStrLn a
  putStrLn b
  print $ needlemanWunsch (VU.fromList a) (VU.fromList b)
  align xs

data Signature m x r c = Signature
  { step_step :: x -> (Z:.c :.c ) -> x
  , step_loop :: x -> (Z:.c :.()) -> x
  , loop_step :: x -> (Z:.():.c ) -> x
  , nil_nil   ::      (Z:.():.()) -> x
  , h         :: Stream m x -> m r
  }

-- grammar :: Signature m x r c -> ???
grammar Signature{..} a i1 i2 =
  ( a, step_step <<< a % (T:!chr i1:!chr i2) |||
       step_loop <<< a % (T:!chr i1:!None  ) |||
       loop_step <<< a % (T:!None  :!chr i2) |||
       nil_nil   <<< (T:!Empty:!Empty)       ... h
  )
{-# INLINE grammar #-}

sScore :: Monad m => Signature m Int Int Char
sScore = Signature
  { step_step = \x (Z:.a:.b) -> if a==b then x+1 else x-1
  , step_loop = \x _         -> x-1
  , loop_step = \x _         -> x-1
  , nil_nil   = const 0
  , h = S.foldl' max 0
  }
{-# INLINE sScore #-}

needlemanWunsch i1 i2 = (ws ! (Z:.pointL 0 n1:.pointL 0 n2), bt) where
  ws = unsafePerformIO (forwardPhase i1 i2)
  n1 = VU.length i1
  n2 = VU.length i2
  bt = [] :: String
{-# NOINLINE needlemanWunsch #-}

forwardPhase :: VU.Vector Char -> VU.Vector Char -> IO (PA.Unboxed (Z:.PointL:.PointL) Int)
forwardPhase i1 i2 = do
  let n1 = VU.length i1
  let n2 = VU.length i2
  !t' <- newWithM (Z:.pointL 0 0:.pointL 0 0) (Z:.pointL 0 n1:.pointL 0 n2) 0
  let t= mTbl (Z:.EmptyT:.EmptyT) t'
  fillTable $ grammar sScore t i1 i2
  freeze t'
{-# INLINE forwardPhase #-}

fillTable (MTbl _ tbl, f) = do
  let (_,Z:.PointL(0:.n1):.PointL(0:.n2)) = boundsM tbl
  forM_ [0 .. n1] $ \k1 -> forM_ [0 .. n2] $ \k2 -> do
    (f $ Z:.pointL 0 k1:.pointL 0 k2) >>= writeM tbl (Z:.pointL 0 k1:.pointL 0 k2)
{-# INLINE fillTable #-}

