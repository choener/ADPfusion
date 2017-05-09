
module ADP.Fusion.Term.Deletion.Point where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Core
import           ADP.Fusion.Core.Point
import           ADP.Fusion.Term.Deletion.Type



instance
  ( TmkCtx1 m ls Deletion (PointL i)
  ) => MkStream m (ls :!: Deletion) (PointL i) where
  mkStream grd (ls :!: Deletion) sv us is
    = S.map (\(ss,ee,ii) -> ElmDeletion ii ss)
    . addTermStream1 Deletion sv us is
    $ mkStream grd ls (termStaticVar Deletion sv is) us (termStreamIndex Deletion sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx m ts s x0 i0 is (PointL I)
  ) => TermStream m (TermSymbol ts Deletion) s (is:.PointL I) where
  termStream (ts:|Deletion) (cs:.IStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiPlI i) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx m ts s x0 i0 is (PointL O)
  ) => TermStream m (TermSymbol ts Deletion) s (is:.PointL O) where
  termStream (ts:|Deletion) (cs:.OStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s ii ee) ->
                let io = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                in  TState s (ii:.: io) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar Deletion (PointL I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (PointL j) = PointL j
  termStaticCheck _ _ = 1#
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

instance TermStaticVar Deletion (PointL O) where
  termStaticVar   _ (OStatic d) _ = OStatic d
  termStreamIndex _ _           j = j
  termStaticCheck _ _ = 1#
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

