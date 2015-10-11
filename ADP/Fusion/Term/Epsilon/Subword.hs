
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
    = map (\(ss,ee,ii,oo) -> ElmEpsilon ii oo ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx1 m ts a is (Subword I)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.Subword I) where
  termStream (ts:|Epsilon) (cs:.IStatic ()) (us:.u) (is:.Subword (i:.j))
    = staticCheck (i==j)
    . map (\(TState s a b ii oo ee) ->
              TState s a b (ii:.subword i j) (oo:.subword 0 0) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (Subword O)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.Subword O) where
  termStream (ts:|Epsilon) (cs:.OStatic d) (us:.Subword (ui:.uj)) (is:.Subword (i:.j))
    = staticCheck (ui == i && uj == j) -- TODO correct ?
    . map (\(TState s a b ii oo ee) ->
              let i' = getIndex a (Proxy :: Proxy (is:.Subword O))
                  o' = getIndex b (Proxy :: Proxy (is:.Subword O))
              in  TState s a b (ii:.i') (oo:.o') (ee:.()) )
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

