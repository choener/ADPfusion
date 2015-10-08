
module ADP.Fusion.Term.Epsilon.Subword where

import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Term.Epsilon.Type

--import Data.Vector.Fusion.Util

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


--instance
--  ( Monad m
--  , MkStream m ls (Subword I)
--  ) => MkStream m (ls :!: Epsilon) (Subword I) where
--  mkStream (ls :!: Epsilon) (IStatic ()) hh ij@(Subword (i:.j))
--    = staticCheck (i==j)
--    $ map (ElmEpsilon (subword i j) (subword 0 0))
--    $ mkStream ls (IStatic ()) hh ij
--  {-# Inline mkStream #-}

--instance
--  ( Monad m
--  , MkStream m ls (Subword O)
--  ) => MkStream m (ls :!: Epsilon) (Subword O) where
--  mkStream (ls :!: Epsilon) (OStatic d) u ij@(Subword (i:.j))
--    = map (ElmEpsilon (subword i j) (subword i j))
--    $ mkStream ls (OStatic d) u ij
--  {-# Inline mkStream #-}



--instance
--  ( Monad m
--  , TerminalStream m a is
--  ) => TerminalStream m (TermSymbol a Epsilon) (is:.Subword I) where
--  terminalStream (a:|Epsilon) (sv:.IStatic _) (is:.ij@(Subword (i:.j)))
--    = S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.subword i j) (os:.subword 0 0) (e:.()))
--    . iPackTerminalStream a sv (is:.ij)
--  {-# Inline terminalStream #-}

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

