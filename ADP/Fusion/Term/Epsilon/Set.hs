
module ADP.Fusion.Term.Epsilon.Set where

import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Term.Epsilon.Type




instance
  ( TmkCtx1 m ls Epsilon (BS2 First Last i)
  ) => MkStream m (ls :!: Epsilon) (BS2 First Last i) where
  mkStream (ls :!: Epsilon) sv us is
    = map (\(ss,ee,ii,oo) -> ElmEpsilon ii oo ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx1 m ts a is (BS2 First Last I)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.BS2 First Last I) where
  termStream (ts:|Epsilon) (cs:.IStatic r) (us:.u) (is:.BS2 bs _ _)
    = staticCheck (bs==0)
    . map (\(TState s a b ii oo ee) ->
              TState s a b (ii:.BS2 0 0 0) (oo:.BS2 0 0 0) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (BS2 First Last O)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.BS2 First Last O) where
  termStream (ts:|Epsilon) (cs:.OStatic r) (us:.BS2 ub uf ul) (is:.BS2 bs f l)
    = staticCheck (ub==bs)
    . map (\(TState s a b ii oo ee) ->
              let i' = getIndex a (Proxy :: Proxy (is:.BS2 First Last O))
                  o' = getIndex b (Proxy :: Proxy (is:.BS2 First Last O))
              in  TState s a b (ii:.i') (oo:.o') (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}

