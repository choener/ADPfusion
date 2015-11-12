
module ADP.Fusion.Term.Deletion.Unit where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Deletion.Type



instance
  ( TmkCtx1 m ls Deletion (Unit i)
  ) => MkStream m (ls :!: Deletion) (Unit i) where
  mkStream (ls :!: Deletion) sv us is
    = S.map (\(ss,ee,ii,oo) -> ElmDeletion ii oo ss)
    . addTermStream1 Deletion sv us is
    $ mkStream ls (termStaticVar Deletion sv is) us (termStreamIndex Deletion sv is)
  {-# Inline mkStream #-}



instance
  ( TstCtx1 m ts a is (Unit I)
  ) => TermStream m (TermSymbol ts Deletion) a (is:.Unit I) where
  termStream (ts:|Deletion) (cs:.IStatic ()) (us:._) (is:._)
    = S.map (\(TState s a b ii oo ee) -> TState s a b (ii:.Unit) (oo:.Unit) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( TstCtx1 m ts a is (Unit O)
  ) => TermStream m (TermSymbol ts Deletion) a (is:.Unit O) where
  termStream (ts:|Deletion) (cs:.OStatic ()) (us:._) (is:._)
    = S.map (\(TState s a b ii oo ee) -> TState s a b (ii:.Unit) (oo:.Unit) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar Deletion (Unit I) where
  termStaticVar _ _ _ = IStatic ()
  termStreamIndex _ _ _ = Unit
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Deletion (Unit O) where
  termStaticVar _ _ _ = OStatic ()
  termStreamIndex _ _ _ = Unit
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

