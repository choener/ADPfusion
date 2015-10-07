
module ADP.Fusion.Term.Strng.Point where

import           Data.Proxy
import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Strng.Type



instance
  ( Monad m
  , MkStream m ls (PointL i)
  , TermStream m (TermSymbol M (Strng v x)) (Z:.PointL i) (Z:.PointL i)
  , Element ls (PointL i)
  , TermStaticVar (Strng v x) (PointL i)
  ) => MkStream m (ls :!: Strng v x) (PointL i) where
  mkStream (ls :!: strng@(Strng _ minL maxL xs)) sv us is
    = S.map (\(ss,ee,ii,oo) -> ElmStrng ee ii oo ss)
    . addTermStream1 strng sv us is
    $ mkStream ls (termStaticVar strng sv is) us (termStreamIndex strng sv is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , GetIndex a (is:.PointL I)
  , GetIx a (is:.PointL I) ~ (PointL I)
  , TermStream m ts a is
  ) => TermStream m (TermSymbol ts (Strng v x)) a (is:.PointL I) where
  termStream (ts:|Strng f minL maxL v) (cs:.IStatic d) (us:.PointL u) (is:.PointL i)
    = S.map (\(TState s a b ii oo ee) ->
                let PointL j = getIndex a (Proxy :: Proxy (is:.PointL I))
                in  TState s a b (ii:.PointL i) (oo:.PointL 0) (ee:.f j (i-j) v))
    . termStream ts cs us is
  {-# Inline termStream #-}

instance
  ( Monad m
  , TermStream m ts a is
  ) => TermStream m (TermSymbol ts (Strng v x)) a (is:.PointL O) where
  termStream (ts:|Strng f minL maxL v) (cs:.OStatic d) (us:.PointL u) (is:.PointL i)
    = error "TODO termStream / Strng / PointL"
    . termStream ts cs us is
  {-# Inline termStream #-}

instance TermStaticVar (Strng v x) (PointL I) where
  termStaticVar (Strng _ minL maxL _) (IStatic   d) _ = IVariable $ d + maxL - minL
  -- TODO need this as well, we want to allow multiple terminals in linear
  -- languages, even if they induce variable boundaries
--  termStaticVar _ (IVariable d) _ = IVariable d
  termStreamIndex (Strng _ minL _ _) (IStatic d) (PointL j) = PointL $ j - minL
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar (Strng v x) (PointL O) where


--instance
--  ( Monad m
--  , Element ls (PointL I)
--  , MkStream m ls (PointL I)
--  ) => MkStream m (ls :!: Strng v x) (PointL I) where
--  mkStream (ls :!: Strng f minL maxL xs) (IStatic d) (PointL u) (PointL i)
--    = staticCheck (i - minL >= 0 && i <= u && minL <= maxL)
--    $ S.map (\z -> let PointL j = getIdx z in ElmStrng (f j (i-j) xs) (PointL i) (PointL 0) z)
--    $ mkStream ls (IVariable $ d + maxL - minL) (PointL u) (PointL $ i - minL)
--  mkStream _ _ _ _ = error "mkStream / Strng / PointL / IVariable"
--  {-# Inline mkStream #-}
--
--instance TermStaticVar (Strng v x) (PointL I) where
--  termStaticVar _ (IStatic   d) _ = IVariable d
--  termStaticVar _ (IVariable d) _ = IVariable d
--  termStreamIndex (Strng _ minL _ _) (IStatic d) (PointL j) = PointL $ j - minL
--  {-# Inline [0] termStaticVar   #-}
--  {-# Inline [0] termStreamIndex #-}
--
--instance
--  ( Monad m
--  , TerminalStream m a is
--  ) => TerminalStream m (TermSymbol a (Strng v x)) (is:.PointL I) where
--  terminalStream (a:|Strng f minL maxL xs) (sv:.IStatic d) (is:.i@(PointL j))
--    = S.map (\(S6 s (zi:.PointL pi) (zo:._) is os e) -> S6 s zi zo (is:.i) (os:.PointL 0) (e:.f pi (j-pi) xs))
--    . iPackTerminalStream a sv (is:.i)
--  {-# Inline terminalStream #-}

