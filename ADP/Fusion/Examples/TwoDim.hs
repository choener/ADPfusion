{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

-- | This is not really a working example, but rather to check the GHC-Core for
-- fusion.

--module ADP.Fusion.Examples.TwoDim where
module Main where

import           Control.Applicative
import           Control.Monad
import           Data.Array.Repa.Index
import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import           Data.Vector.Fusion.Util
import qualified Control.Arrow as A
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import           System.IO.Unsafe (unsafePerformIO)

import Data.Array.Repa.Index.Points
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA
import qualified Data.PrimitiveArray.FillTables as PA

import ADP.Fusion.Chr
import ADP.Fusion.Empty hiding (empty)
import ADP.Fusion hiding (empty)
import ADP.Fusion.Multi
import ADP.Fusion.Table
import ADP.Fusion.TH
import Data.Array.Repa.Index.Subword



data Signature m x r c = Signature
  { step_step :: x -> (Z:.c :.c ) -> x
  , step_loop :: x -> (Z:.c :.()) -> x
  , loop_step :: x -> (Z:.():.c ) -> x
  , nil_nil   ::      (Z:.():.()) -> x
  , h         :: Stream m x -> m r
  }

makeAlgebraProductH ['h] ''Signature

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

-- grammar :: Signature m x r c -> ???
grammar Signature{..} a i1 i2 =
  Z:.
  ( a, step_step <<< a % (M:>chr i1:>chr i2) |||
       step_loop <<< a % (M:>chr i1:>None  ) |||
       loop_step <<< a % (M:>None  :>chr i2) |||
       nil_nil   <<< (M:>Empty:>Empty)       ... h
  )
{-# INLINE grammar #-}

sScore :: Monad m => Signature m Int Int Char
sScore = Signature
  { step_step = \x (Z:.a:.b) -> if a==b then x+1 else x-2
  , step_loop = \x _         -> x-1
  , loop_step = \x _         -> x-1
  , nil_nil   = const 0
  , h = S.foldl' max 0
  }
{-# INLINE sScore #-}

sPretty :: Monad m => Signature m [String] (S.Stream m [String]) Char
sPretty = Signature
  { step_step = \[x,y] (Z:.a :.b ) -> [a  :x, b  :y]
  , step_loop = \[x,y] (Z:.a :.()) -> [a  :x, '-':y]
  , loop_step = \[x,y] (Z:.():.b ) -> ['-':x, b  :y]
  , nil_nil   = const ["",""]
  , h = return . id
  }

needlemanWunsch i1 i2 = (ws PA.! (Z:.pointL 0 n1:.pointL 0 n2), bt) where
  (Z:.ws) = unsafePerformIO (forwardPhase i1 i2)
  n1 = VU.length i1
  n2 = VU.length i2
  bt = backtrack i1 i2 (Z:.ws)
{-# NOINLINE needlemanWunsch #-}

forwardPhase :: VU.Vector Char -> VU.Vector Char -> IO (Z:.(PA.Unboxed (Z:.PointL:.PointL) Int))
forwardPhase i1 i2 = do
  let n1 = VU.length i1
  let n2 = VU.length i2
  !t' <- PA.newWithM (Z:.pointL 0 0:.pointL 0 0) (Z:.pointL 0 n1:.pointL 0 n2) 0
  let t= mTblD (Z:.EmptyOk:.EmptyOk) t'
  PA.runFillTables . expose $ grammar sScore t i1 i2
  PA.freeze t' >>= return . (Z:.)
{-# INLINE forwardPhase #-}

backtrack :: VU.Vector Char -> VU.Vector Char -> (Z:.(PA.Unboxed (Z:.PointL:.PointL) Int)) -> [[String]]
backtrack i1 i2 (Z:.t') = map (map reverse) . unId . S.toList . unId . g $ Z:.pointL 0 n1 :. pointL 0 n2 where
  n1 = VU.length i1
  n2 = VU.length i2
  t = btTblD (Z:.EmptyOk:.EmptyOk) t' g
  (Z:.(_,g)) = grammar (sScore <** sPretty) t i1 i2
{-# NOINLINE backtrack #-}

