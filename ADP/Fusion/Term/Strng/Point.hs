
module ADP.Fusion.Term.Strng.Point where

import           Data.Strict.Tuple
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Strng.Type



instance
  ( Monad m
  , Element ls PointL
  , MkStream m ls PointL
  ) => MkStream m (ls :!: Strng v x) PointL where
  mkStream (ls :!: Strng f minL maxL xs) (IStatic d) (PointL u) (PointL i)
    = staticCheck (i - minL >= 0 && i <= u && minL <= maxL)
    $ S.map (\z -> let PointL j = getIdx z in ElmStrng (f j (i-j) xs) (PointL i) (PointL 0) z)
    $ mkStream ls (IVariable $ d + maxL - minL) (PointL u) (PointL $ i - minL)
  mkStream _ _ _ _ = error "mkStream / Strng / PointL / IVariable"
  {-# Inline mkStream #-}

instance TermStaticVar (Strng v x) PointL where
  termStaticVar _ (IStatic   d) _ = IVariable d
  termStaticVar _ (IVariable d) _ = IVariable d
  termStreamIndex (Strng _ minL _ _) (IStatic d) (PointL j) = PointL $ j - minL
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a (Strng v x)) (is:.PointL) where
  terminalStream (a:|Strng f minL maxL xs) (sv:.IStatic d) (is:.i@(PointL j))
    = S.map (\(S6 s (zi:.PointL pi) (zo:._) is os e) ->
              S6 s zi zo (is:.i) (os:.PointL 0) (e:.f pi (j-pi) xs))
    . iPackTerminalStream a sv (is:.i)
  {-# Inline terminalStream #-}

