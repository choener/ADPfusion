
{-# Options_GHC -fforce-recomp #-}
{-# Options_GHC -Wno-partial-type-signatures #-}

{-# Language MagicHash #-}


module Main (main) where

import           Control.Monad (forM_,when)
import           Debug.Trace
import           System.Environment (getArgs)
import           Text.Printf
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Foldable (maximumBy)
import           Data.Ord (comparing)
import           Data.Ord.Fast
import           GHC.Exts

import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU

import           Data.PrimitiveArray as PA hiding (map)

import           ADPfusion.PointL



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
                  nil_nil   <<< (M:|Epsilon @Local:|Epsilon @Local)       ... h
                )
  in Z:.a
{-# INLINE grammar #-}

fasteq ∷ Char → Char → Int → Int → Int
{-# Inline fasteq #-}
fasteq (C# a) (C# b) (I# x) (I# y) =
  let l = (eqChar# a b)
  in  I# ( (x *# l) +# (y *# (1# -# l)) )

sScore ∷ Monad m ⇒ Signature m Int Int Char
sScore = Signature
  -- { step_step = \x (Z:.a:.b) → if a==b then x + 1 else x-2
  { step_step = \x (Z:.a:.b) → fasteq a b (x+1) (x-2) -- if a==b then x + 1 else x-2
  , step_loop = \x _         → x-1
  , loop_step = \x _         → x-1
  , nil_nil   = const 0
  , h = SM.foldl' fastmax (-999999)
  }
{-# INLINE sScore #-}


sPretty ∷ Monad m ⇒ Signature m [String] [[String]] Char
sPretty = Signature
  { step_step = \[x,y] (Z:.a :.b ) → [a  :x, b  :y]
  , step_loop = \[x,y] (Z:.a :.()) → [a  :x, '-':y]
  , loop_step = \[x,y] (Z:.():.b ) → ['-':x, b  :y]
  , nil_nil   = const ["",""]
  , h = SM.toList
  }
{-# Inline sPretty #-}


runNeedlemanWunsch
  ∷ Int
  → String
  → String
  → ((Z:.PointL I:.PointL I),Int,[[String]],PerfCounter)
runNeedlemanWunsch k i1' i2' = (fst dlocal, snd dlocal, take k bs,perf) where
  i1 = VU.fromList i1'
  i2 = VU.fromList i2'
  n1 = VU.length i1
  n2 = VU.length i2
  Mutated (Z:.t) perf eachPerf = nwInsideForward i1 i2
  dlocal = let TW (ITbl _ t') _ = t
           in unId . SM.foldl' (\(ap,as) (p,s) → if s > as then (p,s) else (ap,as)) (Z:.PointL 0:.PointL 0,0) $ PA.assocsS t'
  bs = nwInsideBacktrack i1 i2 t (fst dlocal)
{-# Noinline runNeedlemanWunsch #-}


nwInsideForward
  ∷ VU.Vector Char
  → VU.Vector Char
  → Mutated (Z:.TwITbl _ _ Id (Dense VU.Vector) (Z:.EmptyOk:.EmptyOk) (Z:.PointL I:.PointL I) Int)
nwInsideForward !i1 !i2 = {-# SCC "nwInsideForward" #-} runST $ do
  arr ← newWithPA (ZZ:..LtPointL n1:..LtPointL n2) (-999999)
  ts ← fillTables $ grammar sScore
                      (ITbl @_ @_ @_ @_ @0 @0 (Z:.EmptyOk:.EmptyOk) arr)
                      i1 i2
  return ts
  where !n1 = VU.length i1
        !n2 = VU.length i2
{-# NoInline nwInsideForward #-}

nwInsideBacktrack
  ∷ VU.Vector Char
  → VU.Vector Char
  → TwITbl _ _ Id (Dense VU.Vector) (Z:.EmptyOk:.EmptyOk) (Z:.PointL I:.PointL I) Int
  → (Z:.PointL I:.PointL I)
  → [[String]]
nwInsideBacktrack i1 i2 t k = {-# SCC "nwInsideBacktrack" #-} unId $ axiomAt b k
  where !(Z:.b) = grammar (sScore <|| sPretty) (toBacktrack t (undefined :: Id a -> Id a)) i1 i2
                    :: Z:.TwITblBt _ _ (Dense VU.Vector) (Z:.EmptyOk:.EmptyOk) (Z:.PointL I:.PointL I) Int Id Id [String]
{-# NoInline nwInsideBacktrack #-}


--runOutsideNeedlemanWunsch
--  ∷ Int
--  → String
--  → String
--  → (Int,[[String]],PerfCounter)
--runOutsideNeedlemanWunsch k i1' i2' = {-# SCC "runOutside" #-} (d, take k . unId $ axiom b, perf) where
--  i1 = VU.fromList i1'
--  i2 = VU.fromList i2'
--  n1 = VU.length i1
--  n2 = VU.length i2
--  Mutated (Z:.t) perf eachPerf = nwOutsideForward i1 i2
--  d = unId $ axiom t
--  !(Z:.b) = grammar (sScore <|| sPretty) (toBacktrack t (undefined :: Id a -> Id a)) i1 i2
--              :: Z:.TwITblBt _ _ (Dense VU.Vector) (Z:.EmptyOk:.EmptyOk) (Z:.PointL O:.PointL O) Int Id Id [String]
--{-# Noinline runOutsideNeedlemanWunsch #-}
--
--
--nwOutsideForward
--  ∷ VU.Vector Char
--  → VU.Vector Char
--  → Mutated (Z:.TwITbl _ _ Id (Dense VU.Vector) (Z:.EmptyOk:.EmptyOk) (Z:.PointL O:.PointL O) Int)
--nwOutsideForward !i1 !i2 = {-# SCC "nwOutsideForward" #-} runST $ do
--  arr ← newWithPA (ZZ:..LtPointL n1:..LtPointL n2) (-999999)
--  ts ← fillTables $ grammar sScore
--                      (ITbl @_ @_ @_ @_ @0 @0 (Z:.EmptyOk:.EmptyOk) arr)
--                      i1 i2
--  return ts
--  where !n1 = VU.length i1
--        !n2 = VU.length i2
--{-# Noinline nwOutsideForward #-}

-- | This wrapper takes a list of input sequences and aligns each odd
-- sequence with the next even sequence. We want one alignment for each
-- such pair.
--
-- Since we use basic lists during backtracking, the resulting lists have
-- to be reversed for inside-backtracking. Note that because the Outside
-- grammar is quasi-right-linear, it does not require reversing the two
-- strings.
--
-- For real applications, consider using @Data.Sequence@ which has @O(1)@
-- append and prepend.

align _ [] = return ()
align _ [c] = putStrLn "single last line"
align (kI,kO) (a:b:xs) = {-# SCC "align" #-} do
  putStrLn a
  putStrLn b
  let (posI,sI,rsI,perfI) = runNeedlemanWunsch kI a b
  when (kI>=0) $ forM_ rsI $ \[u,l] -> printf "%s\n%s\n  %d   %s\n\n" (reverse u) (reverse l) (sI) (show posI)
  when (kI>=0) $ print sI
  when (kI>=0) . putStrLn $ showPerfCounter perfI
  putStrLn ""
  align (kI,kO) xs

-- | And finally have a minimal main that reads from stdio.
--
-- If you are brave enough then put this through @ghc-core@ and look for
-- @nwInsideForward@ or @nwOutsideForward@ in the CORE. Everything coming
-- from the forward phase should be beautifully optimized and the algorithm
-- should run quite fast.

main = do
  as <- getArgs
  let k = case as of
            [] -> (1,1)
            [x] -> let x' = read x
                   in (x',x')
            [x,y] -> let x' = read x; y' = read y
                     in  (x',y')
            args -> error $ "too many arguments"
  ls <- lines <$> getContents
  align k ls

