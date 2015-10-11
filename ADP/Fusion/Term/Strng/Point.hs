
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
  termStream (ts:|Strng f minL maxL v) (cs:.IStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s a b ii oo ee) ->
                let PointL j = getIndex a (Proxy :: Proxy (is:.PointL I))
                in  TState s a b (ii:.PointL i) (oo:.PointL 0) (ee:.f j (i-j) v))
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (PointL O)
  ) => TermStream m (TermSymbol ts (Strng v x)) a (is:.PointL O) where
  termStream (ts:|Strng f minL maxL v) (cs:.OStatic d) (us:.PointL u) (is:.PointL i)
    = error "TODO termStream / Strng / PointL"
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar (Strng v x) (PointL I) where
  termStaticVar (Strng _ minL maxL _) (IStatic   d) _ = IVariable $ d + maxL - minL
  -- TODO need this as well, we want to allow multiple terminals in linear
  -- languages, even if they induce variable boundaries
--  termStaticVar _ (IVariable d) _ = IVariable d
  termStreamIndex (Strng _ minL _ _) (IStatic d) (PointL j) = PointL $ j - minL
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar (Strng v x) (PointL O) where

