
module ADP.Fusion.Term.Epsilon.Subword where

import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Term.Epsilon.Type



instance
  ( TmkCtx1 m ls Epsilon (Subword i)
  ) => MkStream m (ls :!: Epsilon) (Subword i) where
  mkStream (ls :!: Epsilon) sv us is
    = map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx m ts s x0 i0 is (Subword I)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.Subword I) where
  termStream (ts:|Epsilon) (cs:.IStatic ()) (us:.u) (is:.Subword (i:.j))
    = map (\(TState s ii ee) ->
              TState s (ii:.:RiSwI j) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (i==j)
  {-# Inline termStream #-}

instance
  ( TstCtx m ts s xi0 i0 is (Subword O)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.Subword O) where
  termStream (ts:|Epsilon) (cs:.OStatic d) (us:.Subword (ui:.uj)) (is:.Subword (i:.j))
    = staticCheck (ui == i && uj == j) -- TODO correct ?
    . map (\(TState s ii ee) ->
              let io = getIndex (getIdx s) (Proxy :: PRI is (Subword O))
              in  TState s (ii:.:io) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar Epsilon (Subword I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ ij = ij
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Epsilon (Subword O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ ij = ij
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

