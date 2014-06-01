{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Needleman-Wunsch global alignment algorithm. This algorithm is
-- extremely simple but provides a good showcase for what ADPfusion offers.
--
-- We automatically generate the algebra product using
-- 'makeAlgebraProductH'.
--
-- Table filling and freezing is done automatically using 'runFreezeMTbls'
-- as can be seen in the 'forwardPhase' function.

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

import           Data.PrimitiveArray as PA hiding (map)

import           ADP.Fusion



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
  let (s,rs) = needlemanWunsch (VU.fromList a) (VU.fromList b)
  print s
  mapM_ (mapM_ print) rs
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
  , h = S.foldl' max (-999999)
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
  bt = take 1 $ backtrack i1 i2 (Z:.ws)
{-# NOINLINE needlemanWunsch #-}

type Arr  = PA.Unboxed (Z:.PointL:.PointL) Int
type Arrs = Z:.Arr

forwardPhase :: VU.Vector Char -> VU.Vector Char -> IO Arrs
forwardPhase i1 i2 = do
  let n1 = VU.length i1
  let n2 = VU.length i2
  !t' <- PA.newWithM (Z:.pointL 0 0:.pointL 0 0) (Z:.pointL 0 n1:.pointL 0 n2) (-999999)
  let t = mTblD (Z:.EmptyOk:.EmptyOk) t'
  runFreezeMTbls $ grammar sScore t i1 i2
{-# INLINE forwardPhase #-}

backtrack :: VU.Vector Char -> VU.Vector Char -> Arrs -> [[String]]
backtrack i1 i2 (Z:.t') = map (map reverse) . unId . S.toList . unId . g $ Z:.pointL 0 n1 :. pointL 0 n2 where
  n1 = VU.length i1
  n2 = VU.length i2
  t = btTblD (Z:.EmptyOk:.EmptyOk) t' g
  (Z:.(_,g)) = grammar (sScore <** sPretty) t i1 i2
{-# NOINLINE backtrack #-}

