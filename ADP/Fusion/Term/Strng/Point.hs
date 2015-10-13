
module ADP.Fusion.Term.Strng.Point where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Strng.Type



instance
  ( TmkCtx1 m ls (Strng v x) (PointL i)
  ) => MkStream m (ls :!: Strng v x) (PointL i) where
  mkStream (ls :!: strng@(Strng _ minL maxL xs)) sv us is
    = S.map (\(ss,ee,ii,oo) -> ElmStrng ee ii oo ss)
    . addTermStream1 strng sv us is
    $ mkStream ls (termStaticVar strng sv is) us (termStreamIndex strng sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx1 m ts a is (PointL I)
  ) => TermStream m (TermSymbol ts (Strng v x)) a (is:.PointL I) where
  --
  termStream (ts:|Strng f minL maxL v) (cs:.IStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s a b ii oo ee) ->
                let PointL k = getIndex a (Proxy :: Proxy (is:.PointL I))
                in  TState s a b (ii:.PointL i) (oo:.PointL 0) (ee:.f k (i-k) v))
    . termStream ts cs us is
  --
  termStream (ts:|Strng f minL maxL v) (cs:.IVariable d) (us:.PointL u) (is:.PointL i)
    = S.flatten mk step . termStream ts cs us is
    where mk (tstate@(TState s a b ii oo ee)) =
              let PointL k = getIndex a (Proxy :: Proxy (is:.PointL I))
              in  return (tstate, i-k-d-minL)
          step (tstate@(TState s a b ii oo ee), z)
            | z >= 0 && (l-k <= maxL) = return $ S.Yield (TState s a b (ii:.PointL l) (oo:.o) (ee:.f k (l-k+1) v)) (tstate, z-1)
            | otherwise = return $ S.Done
            where PointL k = getIndex a (Proxy :: Proxy (is:.PointL I))
                  o        = PointL 0
                  l        = i - z - d
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (PointL O)
  ) => TermStream m (TermSymbol ts (Strng v x)) a (is:.PointL O) where
  --
  termStream (ts:|Strng f minL maxL v) (cs:.OStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s a b ii oo ee) ->
                let PointL k = getIndex a (Proxy :: Proxy (is:.PointL O))
                    o        = getIndex b (Proxy :: Proxy (is:.PointL O))
                in  TState s a b (ii:.PointL (i-d+1)) (oo:.o) (ee:.f k (i-k) v)) -- @i-d+1 or k-d+1@ ?
    . termStream ts cs us is
  --
  termStream (ts:|Strng f minL maxL v) (cs:.ORightOf d) (us:.PointL u) (is:.PointL i)
    = S.flatten mk step . termStream ts cs us is
    where mk (tstate@(TState s a b ii oo ee)) =
              let PointL k = getIndex a (Proxy :: Proxy (is:.PointL O))
              in  return (tstate, i-k-d-minL)
          step (tstate@(TState s a b ii oo ee), z)
            | z >= 0 && (l-k <= maxL) = return $ S.Yield (TState s a b (ii:.PointL l) (oo:.o) (ee:.f k (l-k+1) v)) (tstate, z-1)
            | otherwise = return $ S.Done
            where PointL k = getIndex a (Proxy :: Proxy (is:.PointL O))
                  o        = getIndex b (Proxy :: Proxy (is:.PointL O))
                  l        = i - z - d
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline termStream #-}



instance TermStaticVar (Strng v x) (PointL I) where
  termStaticVar (Strng _ minL maxL _) (IStatic   d) _ = IVariable $ d + maxL - minL
  termStaticVar _                     (IVariable d) _ = IVariable d -- TODO is this right?
  --
  termStreamIndex (Strng _ minL _ _) (IStatic d) (PointL j) = PointL $ j - minL
  --
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar (Strng v x) (PointL O) where
  termStaticVar (Strng _ minL maxL _) (OStatic  d) _ = ORightOf $ d + maxL - minL
  termStaticVar _                     (ORightOf d) _ = ORightOf 0 -- TODO is this right?
  --
  termStreamIndex _ _ j = j
  --
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

