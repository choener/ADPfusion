
module ADP.Fusion.Term.Epsilon.Unit where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Epsilon.Type



instance
  ( TmkCtx1 m ls Epsilon (Unit i)
  ) => MkStream m (ls :!: Epsilon) (Unit i) where
  mkStream (ls :!: Epsilon) sv us is
    = S.map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx1 m ts a is (Unit I)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.Unit I) where
  termStream (ts:|Epsilon) (cs:.IStatic ()) (us:._) (is:._)
    = S.map (\(TState s a ii ee) -> TState s a (ii:.:RiU) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (Unit O)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.Unit O) where
  termStream (ts:|Epsilon) (cs:.OStatic ()) (us:._) (is:._)
    = S.map (\(TState s a ii ee) -> TState s a (ii:.:RiU) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar Epsilon (Unit I) where
  termStaticVar _ _ _ = IStatic ()
  termStreamIndex _ _ _ = Unit
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Epsilon (Unit O) where
  termStaticVar _ _ _ = OStatic ()
  termStreamIndex _ _ _ = Unit
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

