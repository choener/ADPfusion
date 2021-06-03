
{-# Options_GHC -fforce-recomp #-}
{-# Options_GHC -Wno-partial-type-signatures #-}

-- |

module Main (main) where

import           Control.Monad (forM_,when)
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Ord.Fast
import           Debug.Trace
import           System.Environment (getArgs)
import           Text.Printf
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Storable as VS

import           Data.PrimitiveArray as PA hiding (map)
import qualified Data.PrimitiveArray.Sparse as SS
import           ADPfusion.PointL

import           Data.Ord.Fast



data Signature m x r c = Signature
  { step_step ∷ x → (Z:.c :.c ) → x
  , step_loop ∷ x → (Z:.c :.()) → x
  , loop_step ∷ x → (Z:.():.c ) → x
  , nil_nil   ∷     (Z:.():.()) → x
  , h         ∷ Stream m x -> m r
  }

makeAlgebraProduct ''Signature



grammar Signature{..} !a' !i1 !i2 =
  let a = TW a' ( step_step <<< a % (M:|chr i1:|chr i2)     |||
                  step_loop <<< a % (M:|chr i1:|Deletion  ) |||
                  loop_step <<< a % (M:|Deletion  :|chr i2) |||
                  nil_nil   <<< (M:|Epsilon @Global:|Epsilon @Global)       ... h
                )
  in Z:.a
{-# INLINE grammar #-}



sScore ∷ Monad m ⇒ Signature m Int Int Char
sScore = Signature
  { step_step = \x (Z:.a:.b)  -> {- traceShow (x,a,b)  $ -} if a==b then x+7 else x-5
  , step_loop = \x (Z:.a:.()) -> {- traceShow (x,a,()) $ -} x-3
  , loop_step = \x (Z:.():.b) -> {- traceShow (x,(),b) $ -} x-2
  , nil_nil   = const 0
  , h = SM.foldl' max (-999999)
--  , h = SM.foldl1' fastmax
  }
{-# INLINE sScore #-}

-- | Scores alone are not enough, we also want to pretty-print alignments.

sPretty ∷ Monad m ⇒ Signature m [String] [[String]] Char
sPretty = Signature
  { step_step = \[x,y] (Z:.a :.b ) → [a  :x, b  :y]
  , step_loop = \[x,y] (Z:.a :.()) → [a  :x, '-':y]
  , loop_step = \[x,y] (Z:.():.b ) → ['-':x, b  :y]
  , nil_nil   = const ["",""]
  , h = SM.toList
  }
{-# Inline sPretty #-}

-- | 

runNeedlemanWunsch
  ∷ Int
  -> Int
  → String
  → String
  → (Int,[[String]],PerfCounter)
runNeedlemanWunsch cutoff k i1' i2' = (d, take k bs,perf) where
  i1 = VU.fromList i1'
  i2 = VU.fromList i2'
  n1 = VU.length i1
  n2 = VU.length i2
  Mutated (Z:.t) perf eachPerf = nwInsideForward cutoff i1 i2
  d = unId $ axiom t
  bs = nwInsideBacktrack i1 i2 t
{-# Noinline runNeedlemanWunsch #-}

-- | 

nwInsideForward
  ∷ Int
  -> VU.Vector Char
  → VU.Vector Char
  → Mutated (Z:.TwITbl _ _ Id (SS.Sparse VU.Vector VU.Vector) (Z:.EmptyOk:.EmptyOk) (Z:.PointL I:.PointL I) Int)
nwInsideForward !cutoff !i1 !i2 = {-# SCC "nwInsideForward" #-} runST $ do
  let band :: VU.Vector (Z:.PointL I:.PointL I)
      -- Provide a band of values around the main diagonal
      band = VU.fromList [ (Z:.PointL k:.PointL l)
                         | k <- [0..n1]
                         , l <- [0..n2]
                         , let q :: Double = fromIntegral n1 / fromIntegral n2
                         , let p :: Double = fromIntegral k / fromIntegral (max 1 l)
                         -- , traceShow (k,l,q,p) $ (1-α)*q <= p && (1+α)*q >= p
                         , abs (k-l) <= cutoff
                         ]
      α = 1.0
  arr ← newWithSPA (ZZ:..LtPointL n1:..LtPointL n2) band (-999999)
  ts ← fillTables $ grammar sScore
                      (ITbl @_ @_ @_ @_ @0 @0 (Z:.EmptyOk:.EmptyOk) arr)
                      i1 i2
  --let SS.Sparse{..} = arr in traceShow (PA.assocs arr) $ return ()
  --let SS.Sparse{..} = arr in traceShow ("ixs", sparseIndices) $ return ()
  --let SS.Sparse{..} = arr in traceShow ("dta", sparseData) $ return ()
  --let SS.Sparse{..} = arr in traceShow ("man", manhattanStart) $ return ()
  return ts
  where !n1 = VU.length i1
        !n2 = VU.length i2
{-# NoInline nwInsideForward #-}

nwInsideBacktrack
  ∷ VU.Vector Char
  → VU.Vector Char
  → TwITbl _ _ Id (SS.Sparse VU.Vector VU.Vector) (Z:.EmptyOk:.EmptyOk) (Z:.PointL I:.PointL I) Int
  → [[String]]
nwInsideBacktrack i1 i2 t = {-# SCC "nwInsideBacktrack" #-} unId $ axiom b
  where !(Z:.b) = grammar (sScore <|| sPretty) (toBacktrack t (undefined :: Id a -> Id a)) i1 i2
                    :: Z:.TwITblBt _ _ (SS.Sparse VU.Vector VU.Vector) (Z:.EmptyOk:.EmptyOk) (Z:.PointL I:.PointL I) Int Id Id [String]
{-# NoInline nwInsideBacktrack #-}

-- | 

align _ _ [] = return ()
align _ _ [c] = putStrLn "single last line"
align cutoff kI (a:b:xs) = {-# SCC "align" #-} do
  let lenA = length a
      lenB = length b
      minCut = abs $ lenA - lenB
  putStrLn a
  putStrLn b
  let (sI,rsI,perfI) = runNeedlemanWunsch (minCut + cutoff) kI a b
  when (kI>=0) $ forM_ rsI $ \[u,l] -> printf "%s\n%s  %d\n\n" (reverse u) (reverse l) sI
  when (kI>=0) $ print sI
  when (kI>=0) . putStrLn $ showPerfCounter perfI
  putStrLn ""
  align cutoff kI xs

-- | 

main = do
  as <- getArgs
  let (cutoff, k) = case as of
            [] -> (30,1)
            [c,x] -> (read c, read x)
            args -> error $ "too many arguments"
  ls <- lines <$> getContents
  align cutoff k ls



test = align 3 1 ["a","a"]
