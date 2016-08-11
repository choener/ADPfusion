
-- | Lets try to get a grip on what specconstr does to our code.

module Main (main) where

import           Control.Applicative
import           Control.Monad
import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Control.Arrow as A
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Environment (getArgs)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Printf

import           Data.PrimitiveArray as PA hiding (map)

import           ADP.Fusion.Point




data Signature m x r c = Signature
  { step_step :: x -> (Z:.c :.c ) -> x
  , step_loop :: x -> (Z:.c :.()) -> x
  , loop_step :: x -> (Z:.():.c ) -> x
  , nil_nil   ::      (Z:.():.()) -> x
  , booboo    :: x -> (Z:.c:.c) -> (Z:.c:.c) -> (Z:.c:.c) -> (Z:.c:.c) -> x
  , h         :: Stream m x -> m r
  }



grammar Signature{..} a' i1 i2 =
  let a = a'  ( --step_step <<< a % (M:|chr i1:|chr i2)     |||
--                step_loop <<< a % (M:|chr i1:|Deletion  ) |||
--                loop_step <<< a % (M:|Deletion  :|chr i2) |||
                step_step <<< a % (M:|chr i1:|chr i2)     |||
--                step_step <<< a % (M:|chr i1:|chr i2)     |||
--                step_step <<< a % (M:|chr i1:|chr i2)     |||
--                step_step <<< a % (M:|chr i1:|chr i2)     |||
--                step_step <<< a % (M:|chr i1:|chr i2)     |||
--                step_step <<< a % (M:|chr i1:|chr i2)     |||
--                step_step <<< a % (M:|chr i1:|chr i2)     |||
--                step_step <<< a % (M:|chr i1:|chr i2)     |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                booboo    <<< a % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2) % (M:|chr i1:|chr i2)    |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
--                nil_nil   <<< (M:|Epsilon:|Epsilon)       |||
                nil_nil   <<< (M:|Epsilon:|Epsilon)       ... h
              )
  in Z:.a
{-# INLINE grammar #-}


sScore :: Monad m => Signature m Int Int Char
sScore = Signature
  { step_step = \x (Z:.a:.b) -> if a==b then x+1 else x-2
  , step_loop = \x _         -> x-1
  , loop_step = \x _         -> x-1
  , nil_nil   = const 0
  , booboo    = \x _ _ _ _   -> x
  , h = SM.foldl' max (-999999)
  }
{-# INLINE sScore #-}


runNeedlemanWunsch :: Int -> String -> String -> Int
runNeedlemanWunsch k i1' i2' = d where
  i1 = VU.fromList i1'
  i2 = VU.fromList i2'
  n1 = VU.length i1
  n2 = VU.length i2
  !(Z:.t) = nwInsideForward i1 i2
  d = unId $ axiom t
{-# Noinline runNeedlemanWunsch #-}

nwInsideForward :: VU.Vector Char -> VU.Vector Char -> Z:.ITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.PointL I:.PointL I) Int
nwInsideForward i1 i2 = {-# SCC "nwInsideForward" #-} mutateTablesDefault $
                          grammar sScore
                          (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.PointL 0:.PointL 0) (Z:.PointL n1:.PointL n2) (-999999) []))
                          i1 i2
  where n1 = VU.length i1
        n2 = VU.length i2
{-# NoInline nwInsideForward #-}

main = do
  ls <- lines <$> getContents
  print $ runNeedlemanWunsch 1 (ls!!0) (ls!!1)


