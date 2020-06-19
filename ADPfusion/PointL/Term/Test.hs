
module ADPfusion.PointL.Term.Test where

import           Control.DeepSeq
import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           GHC.Exts

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Core.Term.Test
import           ADPfusion.Point.Core



instance
  ( TmkCtx1 m ls (Test v x) (PointL i)
  ) => MkStream m (ls :!: Test v x) (PointL i) where
  mkStream grd (ls :!: strng) sv us is
    = S.map (\(ss,ee,ii) -> ElmTest ee ii ss)
    . addTermStream1 strng sv us is
    $ mkStream (grd `andI#` termStaticCheck strng is) ls (termStaticVar strng sv is) us (termStreamIndex strng sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx m ts s x0 i0 is (PointL I)
  ) => TermStream m (TermSymbol ts (Test v x)) s (is:.PointL I) where
  --
  termStream (ts:|Test (!v)) (cs:.IStatic d) (us:..LtPointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let RiPlI !k = getIndex (getIdx s) (Proxy :: PRI is (PointL I))
                in  TState s (ii:.:RiPlI i) (ee:.VG.unsafeSlice k (i-k) v))
    . termStream ts cs us is
  --
  termStream (ts:|Test (!v)) (cs:.IVariable d) (us:..LtPointL u) (is:.PointL i)
    -- FIXME simplified for 8.2 tests
    = S.flatten mk step . termStream ts cs us is
    where mk (TState s ii ee) =
              let RiPlI !k = getIndex (getIdx s) (Proxy :: PRI is (PointL I))
              in  return (s :!: ii :!: ee :!: k)
          step (s :!: ii :!: ee :!: k)
            | k <= i    = return $ S.Yield (TState s (ii:.:RiPlI k) (ee:.VG.unsafeSlice k (i-k) v))
                                           (s :!: ii :!: ee :!: (k+1))
            | otherwise = return $ S.Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline termStream #-}

{-
instance
  ( TstCtx m ts s x0 i0 is (PointL O)
  ) => TermStream m (TermSymbol ts (Test v x)) s (is:.PointL O) where
  --
  termStream (ts:|Test f minL maxL v) (cs:.OStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let RiPlO k o = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.:RiPlO (i-d+1) o) (ee:.f k (i-k) v)) -- @i-d+1 or k-d+1@ ?
    . termStream ts cs us is
  --
  termStream (ts:|Test f minL maxL v) (cs:.ORightOf d) (us:.PointL u) (is:.PointL i)
    = S.flatten mk step . termStream ts cs us is
    where mk (tstate@(TState s ii ee)) =
              let RiPlO k _ = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
              in  return (tstate, i-k-d-minL)
          step (tstate@(TState s ii ee), z)
            | z >= 0 && (l-k <= maxL) = return $ S.Yield (TState s (ii:.:RiPlO l o) (ee:.f k (l-k+1) v)) (tstate, z-1)
            | otherwise = return $ S.Done
            where RiPlO k o = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                  l         = i - z - d
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline termStream #-}
-}


instance TermStaticVar (Test v x) (PointL I) where
  termStaticVar (Test _) (IStatic   d) _ = IVariable d
  termStaticVar _         (IVariable d) _ = IVariable d
  --
  termStreamIndex (Test _) (IStatic   d) (PointL j) = PointL j
  termStreamIndex (Test _) (IVariable d) (PointL j) = PointL j
  --
  termStaticCheck (Test v) (PointL i) = 1# -- if VG.length v > i then 1# else 0#
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

{-
instance TermStaticVar (Test v x) (PointL O) where
  termStaticVar (Test _ minL maxL _) (OStatic  d) _ = ORightOf $ d + maxL - minL
  termStaticVar _                     (ORightOf d) _ = ORightOf 0 -- TODO is this right?
  --
  termStreamIndex _ _ j = j
  --
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}
-}

