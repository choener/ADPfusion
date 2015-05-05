
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
    = staticCheck (i - minL >= 0 && i + minL <= u && minL <= maxL)
    $ S.map (\z -> let PointL j = getIdx z in ElmStrng (f j (i-j) xs) (PointL i) (PointL 0) z)
    $ mkStream ls (IVariable $ d + maxL - minL) (PointL u) (PointL $ i - minL)
  {-# Inline mkStream #-}

