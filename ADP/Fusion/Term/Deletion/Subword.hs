
module ADP.Fusion.Term.Deletion.Subword where

import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Term.Deletion.Type



instance
  ( TmkCtx1 m ls Deletion (Subword i)
  ) => MkStream m (ls :!: Deletion) (Subword i) where
  mkStream (ls :!: Deletion) sv us is
    = map (\(ss,ee,ii,oo) -> ElmDeletion ii oo ss)
    . addTermStream1 Deletion sv us is
    $ mkStream ls (termStaticVar Deletion sv is) us (termStreamIndex Deletion sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx1 m ts a is (Subword I)
  ) => TermStream m (TermSymbol ts Deletion) a (is:.Subword I) where
  termStream (ts:|Deletion) (cs:.IStatic d) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a b ii oo ee) -> TState s a b (ii:.subword j j) (oo:.subword 0 0) (ee:.()) )
    . termStream ts cs us is
  termStream (ts:|Deletion) (cs:.IVariable d) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a b ii oo ee) ->
                let Subword (_:.l) = getIndex a (Proxy :: Proxy (is:.Subword I))
                in  TState s a b (ii:.subword l l) (oo:.subword 0 0) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (Subword O)
  ) => TermStream m (TermSymbol ts Deletion) a (is:.Subword O) where
  -- X_ij  -> Y_ik  Z_kj  d_jj        0   i Y k Z j-j   N
  -- Y^_ik -> X^_ij Z_kj  d_jj        0 x i   k Z j-j x N
  -- Z^_kj -> Y_ik  X^_ij d_jj        0 x i Y k   j-j x N
  termStream (ts:|Deletion) (cs:.OStatic (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a b ii oo ee) ->
                let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword O))
                    o              = getIndex b (Proxy :: Proxy (is:.Subword O))
                in  TState s a b (ii:.subword k k) (oo:.o) (ee:.()) )
    . termStream ts cs us is
  --
  termStream (ts:|Deletion) (cs:.ORightOf (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a b ii oo ee) ->
                let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword O))
                    o              = getIndex b (Proxy :: Proxy (is:.Subword O))
                    l              = k - dj -- TODO needed ?
                in  TState s a b (ii:.subword k k) (oo:.o) (ee:.()) )
    . termStream ts cs us is
  --
  termStream (ts:|Deletion) (cs:.OFirstLeft (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a b ii oo ee) ->
                let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword O))
                    o              = getIndex b (Proxy :: Proxy (is:.Subword O))
                in  TState s a b (ii:.subword k k) (oo:.o) (ee:.()) )
    . termStream ts cs us is
  --
  termStream (ts:|Deletion) (cs:.OLeftOf (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a b ii oo ee) ->
                let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword O))
                    o              = getIndex b (Proxy :: Proxy (is:.Subword O))
                in  TState s a b (ii:.subword k k) (oo:.o) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar Deletion (Subword I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ ij = ij
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Deletion (Subword O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ ij = ij
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

