
{-# Options_GHC -fdicts-cheap                  #-}
{-# Options_GHC -flate-dmd-anal                #-}
{-# Options_GHC -fmax-worker-args=1000         #-}
{-# Options_GHC -fspec-constr-count=20000      #-}
{-# Options_GHC -fspec-constr-keen             #-}
{-# Options_GHC -fspec-constr-recursive=20000  #-}
{-# Options_GHC -fspec-constr-threshold=1000   #-}
{-# Options_GHC -Wno-partial-type-signatures   #-}
-- both, full laziness and no liberate case are essential to have things inline nicely!
{-# Options_GHC -fno-full-laziness             #-}
{-# Options_GHC -fno-liberate-case             #-}

{-# Language RecordWildCards #-}
{-# Language NoMonomorphismRestriction #-}

module Main where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ST
import           Data.Char (toUpper,toLower)
import           Data.List as L
import           Data.Vector.Fusion.Util
import           Debug.Trace
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           System.Environment (getArgs)
import           Text.Printf

import           Data.PrimitiveArray as PA

import           ADPfusion.Core
import           ADPfusion.PointL



data Tup m x r c = Tup
--  { pkk :: (Z:.c) -> x -> x
  { nll :: (()) -> x
--  , sng :: (Z:.()) -> x
  , h   :: SM.Stream m x -> m r
  }

makeAlgebraProduct ''Tup


bpmax :: Monad m => Tup m Int Int Char
bpmax = Tup
--  { pkk = \ (Z:.c) x -> x + 123456
  { nll = \ (()) -> 987654
--  , sng = \ (Z:.()) -> 0
  , h   = SM.foldl' max (-999999)
  }
{-# INLINE bpmax #-}

-- |

grammar Tup{..} s' t' c =
  let s = TW s' ( -- pkk <<< (M:|c) % s       |||
                  nll <<< (Epsilon @Global) ... h
                )
      t = TW t' ( nll <<< (Epsilon @Global) ... h )
  in Z:.s:.t
{-# INLINE grammar #-}


type A1 = TwITbl 0 0 Id (Dense VU.Vector) (EmptyOk) (PointL I) Int
type T = TwITbl 0 0 Id (Dense VU.Vector) (Z:.EmptyOk) (Z:.PointL I) Int

runInsideForward :: VU.Vector Char -> Mutated (Z:.A1:.A1)
runInsideForward i = runST $ do
  let n = VU.length i
  arr0 <- newWithPA (LtPointL n) (-777777)
  --arr1 <- newWithPA (ZZ:..LtPointL n) (-888888)
  let guideIndex = Z:.BOI @0 (upperBound arr0)
  fillTables {- Dim guideIndex -} $ grammar bpmax
    (ITbl @_ @_ @_ @_ @_ @_ (EmptyOk) arr0)
    (ITbl @_ @_ @_ @_ @_ @_ (EmptyOk) arr0)
    (chr i)
  where n = VU.length i
{-# NoInline runInsideForward #-}

main :: IO ()
main = do
  as <- getArgs
  let k = if null as then 1 else read $ head as
  ls <- lines <$> getContents
  forM_ ls $ \l -> do
    print $ length l
    let Mutated zt perf _ = runInsideForward $ VU.fromList l
    print $ showPerfCounter perf

