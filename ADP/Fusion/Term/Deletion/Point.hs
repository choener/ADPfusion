
module ADP.Fusion.Term.Deletion.Point where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Deletion.Type



instance
  ( Monad m
  , MkStream m ls (PointL i)
  , TermStream m (TermSymbol M Deletion) (Z:.PointL i) (Z:.PointL i)
  , Element ls (PointL i)
  , TermStaticVar Deletion (PointL i)
  ) => MkStream m (ls :!: Deletion) (PointL i) where
  mkStream (ls :!: Deletion) sv us is
    = S.map (\(ss,ee,ii,oo) -> ElmDeletion ii oo ss)
    . addTermStream1 Deletion sv us is
    $ mkStream ls (termStaticVar Deletion sv is) us (termStreamIndex Deletion sv is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , TermStream m ts a is
  ) => TermStream m (TermSymbol ts Deletion) a (is:.PointL I) where
  termStream (ts:|Deletion) (cs:.IStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s a b ii oo ee) -> TState s a b (ii:.PointL i) (oo:.PointL 0) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( Monad m
  , TermStream m ts a is
  , GetIndex a (is:.PointL O)
  , GetIx a (is:.PointL O) ~ (PointL O)
  ) => TermStream m (TermSymbol ts Deletion) a (is:.PointL O) where
  termStream (ts:|Deletion) (cs:.OStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s a b ii oo ee) ->
                let i' = getIndex a (Proxy :: Proxy (is:.PointL O))
                    o' = getIndex b (Proxy :: Proxy (is:.PointL O))
                in  TState s a b (ii:.i') (oo:.o') (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}

--instance
--  ( Monad m
--  , MkStream m ls (PointL I)
--  ) => MkStream m (ls :!: Deletion) (PointL I) where
--  mkStream (ls :!: Deletion) (IStatic d) u i
--    = S.map (ElmDeletion i (PointL 0))
--    $ mkStream ls (IStatic d) u i
--  {-# Inline mkStream #-}
--
--instance
--  ( Monad m
--  , Element ls (PointL O)
--  , MkStream m ls (PointL O)
--  ) => MkStream m (ls :!: Deletion) (PointL O) where
--  mkStream (ls :!: Deletion) (OStatic d) u i
--    = S.map (\z -> ElmDeletion i (getOmx z) z)
--    $ mkStream ls (OStatic d) u i
--  {-# Inline mkStream #-}

instance TermStaticVar Deletion (PointL I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (PointL j) = PointL j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

instance TermStaticVar Deletion (PointL O) where
  termStaticVar   _ (OStatic d) _ = OStatic d
  termStreamIndex _ _           j = j
  {-# Inline termStaticVar #-}
  {-# Inline termStreamIndex #-}

--instance
--  ( Monad m
--  , TerminalStream m a is
--  ) => TerminalStream m (TermSymbol a Deletion) (is:.PointL I) where
--  terminalStream (a:|Deletion) (sv:.IStatic _) (is:.i@(PointL j))
--    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.PointL j) (os:.PointL 0) (e:.()))
--    . iPackTerminalStream a sv (is:.i)
--  {-# Inline terminalStream #-}
--
--instance
--  ( Monad m
--  , TerminalStream m a is
--  ) => TerminalStream m (TermSymbol a Deletion) (is:.PointL O) where
--  terminalStream (a:|Deletion) (sv:.OStatic d) (is:.i)
--    = S.map (\(S6 s (zi:._) (zo:.PointL k) is os e) -> S6 s zi zo (is:.(PointL $ k-d)) (os:.PointL k) (e:.()))
--    . iPackTerminalStream a sv (is:.i)
--  {-# Inline terminalStream #-}

