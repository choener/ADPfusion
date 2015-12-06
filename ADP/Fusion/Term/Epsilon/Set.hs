
module ADP.Fusion.Term.Epsilon.Set where

import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Term.Epsilon.Type



-- ** No boundaries

instance
  ( TmkCtx1 m ls Epsilon (BitSet i)
  ) => MkStream m (ls :!: Epsilon) (BitSet i) where
  mkStream (ls :!: Epsilon) sv us is
    = map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx1 m ts a is (BitSet I)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.BitSet I) where
  termStream (ts:|Epsilon) (cs:.IStatic r) (us:.u) (is:.i)
    = staticCheck (i==0)
    . map (\(TState s a ii ee) ->
              TState s a (ii:.:RiBsI 0) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (BitSet O)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.BitSet O) where
  termStream (ts:|Epsilon) (cs:.OStatic r) (us:.u) (is:.i)
    = staticCheck (i==u)
    . map (\(TState s a ii ee) ->
              TState s a (ii:.:RiBsO u u) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar Epsilon (BitSet I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ b = b
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Epsilon (BitSet O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ b = b
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}



-- ** Two boundaries

instance
  ( TmkCtx1 m ls Epsilon (BS2 First Last i)
  ) => MkStream m (ls :!: Epsilon) (BS2 First Last i) where
  mkStream (ls :!: Epsilon) sv us is
    = map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx1 m ts a is (BS2 First Last I)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.BS2 First Last I) where
  termStream (ts:|Epsilon) (cs:.IStatic r) (us:.u) (is:.BS2 bs _ _)
    = staticCheck (bs==0)
    . map (\(TState s a ii ee) ->
              TState s a (ii:.:RiBs2I (BS2 0 0 0)) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (BS2 First Last O)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.BS2 First Last O) where
  termStream (ts:|Epsilon) (cs:.OStatic r) (us:.BS2 ub uf ul) (is:.BS2 bs f l)
    = staticCheck (ub==bs)
    . map (\(TState s a ii ee) ->
              let io = getIndex a (Proxy :: PRI is (BS2 First Last O))
              in  TState s a (ii:.:io) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}

