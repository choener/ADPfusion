
module ADP.Fusion.Term.Epsilon.Point where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Core
import           ADP.Fusion.Core.Point
import           ADP.Fusion.Term.Epsilon.Type



instance
  ( TmkCtx1 m ls Epsilon (PointL i)
  ) => MkStream m (ls :!: Epsilon) (PointL i) where
  mkStream (ls :!: Epsilon) sv us is
    = S.map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx m ts s x0 i0 is (PointL I)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.PointL I) where
  termStream (ts:|Epsilon) (cs:.IStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPlI i) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx m ts s x0 i0 is (PointL O)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.PointL O) where
  termStream (ts:|Epsilon) (cs:.OStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let io = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.:io) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar Epsilon (PointL I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (PointL j) = PointL j
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Epsilon (PointL O) where
  termStaticVar   _ (OStatic d) _ = OStatic d
  termStreamIndex _ _           j = j
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

