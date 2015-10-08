
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


--instance
--  ( Monad m
--  , TerminalStream m a is
--  ) => TerminalStream m (TermSymbol a Deletion) (is:.Subword I) where
--  terminalStream (a:|Deletion) (sv:.IStatic _) (is:.ij@(Subword (i:.j)))
--    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.subword j j) (os:.subword 0 0) (e:.()))
--    . iPackTerminalStream a sv (is:.ij)
--  terminalStream (a:|Deletion) (sv:.IVariable _) (is:.ij@(Subword (i:.j)))
--    = S.map (\(S6 s (zi:.Subword (_:.l)) (zo:._) is os e) -> S6 s zi zo (is:.subword l l) (os:.subword 0 0) (e:.()))
--    . iPackTerminalStream a sv (is:.ij)
--  {-# Inline terminalStream #-}

instance TermStaticVar Deletion (Subword I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ ij = ij
  {-# Inline termStaticVar   #-}
  {-# Inline termStreamIndex #-}

