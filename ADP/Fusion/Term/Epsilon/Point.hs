
module ADP.Fusion.Term.Epsilon.Point where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Epsilon.Type



instance
  ( Monad m
  , MkStream m ls (PointL i)
  , TermStream m (TermSymbol M Epsilon) (Z:.PointL i) (Z:.PointL i)
  , Element ls (PointL i)
  , TermStaticVar Epsilon (PointL i)
  ) => MkStream m (ls :!: Epsilon) (PointL i) where
  mkStream (ls :!: Epsilon) sv us is
    = S.map (\(ss,ee,ii,oo) -> ElmEpsilon ii oo ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , TermStream m ts a is
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.PointL I) where
  termStream (ts:|Epsilon) (cs:.IStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s a b ii oo ee) -> TState s a b (ii:.PointL i) (oo:.PointL 0) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( Monad m
  , TermStream m ts a is
  , GetIndex a (is:.PointL O)
  , GetIx a (is:.PointL O) ~ (PointL O)
  ) => TermStream m (TermSymbol ts Epsilon) a (is:.PointL O) where
  termStream (ts:|Epsilon) (cs:.OStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s a b ii oo ee) ->
                let i' = getIndex a (Proxy :: Proxy (is:.PointL O))
                    o' = getIndex b (Proxy :: Proxy (is:.PointL O))
                in  TState s a b (ii:.i') (oo:.o') (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}

--instance
--  ( Monad m
--  , MkStream m ls (PointL I)
--  ) => MkStream m (ls :!: Epsilon) (PointL I) where
--  mkStream (ls :!: Epsilon) (IStatic d) (PointL u) (PointL i)
--    = S.map (ElmEpsilon (PointL i) (PointL 0))
--    $ mkStream ls (IStatic d) (PointL u) (PointL i)
--  {-# Inline mkStream #-}
--
--instance
--  ( Monad m
--  , Element ls (PointL O)
--  , MkStream m ls (PointL O)
--  ) => MkStream m (ls :!: Epsilon) (PointL O) where
--  mkStream (ls :!: Epsilon) (OStatic d) (PointL u) (PointL i)
--    = S.map (\z -> ElmEpsilon (PointL i) (getOmx z) z)
--    $ mkStream ls (OStatic d) (PointL u) (PointL i)
--  {-# Inline mkStream #-}

instance TermStaticVar Epsilon (PointL I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (PointL j) = PointL j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance TermStaticVar Epsilon (PointL O) where
  termStaticVar   _ (OStatic d) _ = OStatic d
  termStreamIndex _ _           j = j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

--instance
--  ( Monad m
--  , TerminalStream m a is
--  ) => TerminalStream m (TermSymbol a Epsilon) (is:.PointL I) where
--  terminalStream (a:|Epsilon) (sv:.IStatic _) (is:.i@(PointL j))
--    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.PointL j) (os:.PointL 0) (e:.()))
--    . iPackTerminalStream a sv (is:.i)
--  {-# Inline terminalStream #-}
--
--instance
--  ( Monad m
--  , TerminalStream m a is
--  ) => TerminalStream m (TermSymbol a Epsilon) (is:.PointL O) where
--  terminalStream (a:|Epsilon) (sv:.OStatic d) (is:.i)
--    = S.map (\(S6 s (zi:._) (zo:.PointL k) is os e) -> S6 s zi zo (is:.(PointL $ k-d)) (os:.PointL k) (e:.()))
--    . iPackTerminalStream a sv (is:.i)
--  {-# Inline terminalStream #-}

