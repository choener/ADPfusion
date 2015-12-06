
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
    = map (\(ss,ee,ii) -> ElmDeletion ii ss)
    . addTermStream1 Deletion sv us is
    $ mkStream ls (termStaticVar Deletion sv is) us (termStreamIndex Deletion sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx1 m ts a is (Subword I)
  ) => TermStream m (TermSymbol ts Deletion) a (is:.Subword I) where
  termStream (ts:|Deletion) (cs:.IStatic d) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a ii ee) -> TState s a (ii:.:RiSwI j) (ee:.()) )
    . termStream ts cs us is
  termStream (ts:|Deletion) (cs:.IVariable d) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a ii ee) ->
                let l = getIndex a (Proxy :: PRI is (Subword I))
                in  TState s a (ii:.:l) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (Subword O)
  ) => TermStream m (TermSymbol ts Deletion) a (is:.Subword O) where
  -- X_ij  -> Y_ik  Z_kj  d_jj        0   i Y k Z j-j   N
  -- Y^_ik -> X^_ij Z_kj  d_jj        0 x i   k Z j-j x N
  -- Z^_kj -> Y_ik  X^_ij d_jj        0 x i Y k   j-j x N
  termStream (ts:|Deletion) (cs:._) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a ii ee) ->
                let RiSwO _ k oi oj = getIndex a (Proxy :: PRI is (Subword O))
                in  TState s a (ii:.:RiSwO k k oi oj) (ee:.()) )
    . termStream ts cs us is
  {-
  termStream (ts:|Deletion) (cs:.OStatic (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a ii ee) ->
                let RiSwO _ k oi oj = getIndex a (Proxy :: PRI is (Subword O))
                in  TState s a (ii:.:RiSwO k k oi oj) (ee:.()) )
    . termStream ts cs us is
  --
  termStream (ts:|Deletion) (cs:.ORightOf (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a ii ee) ->
                let RiSwO _ k oi oj = getIndex a (Proxy :: PRI is (Subword O))
                in  TState s a (ii:.:RiSwO k k oi oj) (ee:.()) )
    . termStream ts cs us is
  --
  termStream (ts:|Deletion) (cs:.OFirstLeft (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a ii ee) ->
                let RiSwO _ k oi oj = getIndex a (Proxy :: PRI is (Subword O))
                in  TState s a (ii:.:RiSwO k k oi oj) (ee:.()) )
    . termStream ts cs us is
  --
  termStream (ts:|Deletion) (cs:.OLeftOf (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = S.map (\(TState s a ii ee) ->
                let RiSwO _ k oi oj = getIndex a (Proxy :: PRI is (Subword O))
                in  TState s a (ii:.: RiSwO k k oi oj) (ee:.()) )
    . termStream ts cs us is
  -}
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

