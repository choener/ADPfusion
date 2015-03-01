
module ADP.Fusion.Table.Array.Type where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic (map)
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Table.Indices



-- | Immutable table.

data ITbl m arr i x where
  ITbl :: { iTblConstraint :: !(TblConstraint i)
          , iTblArray      :: !(arr i x)
          , iTblFun        :: !(i -> i -> m x)
          } -> ITbl m arr i x

instance Build (ITbl m arr i x)

instance Element ls i => Element (ls :!: ITbl m arr j x) i where
  data Elm (ls :!: ITbl m arr j x) i = ElmITbl !x !i !i !(Elm ls i)
  type Arg (ls :!: ITbl m arr j x)   = Arg ls :. x
  getArg (ElmITbl x _ _ ls) = getArg ls :. x
  getIdx (ElmITbl _ i _ _ ) = i
  getOmx (ElmITbl _ _ o _ ) = o
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , MkStream m ls (is:.i)
  , PrimArrayOps arr (is:.i) x
  ) => MkStream m (ls :!: ITbl m arr (is:.i) x) (is:.i) where
  mkStream (ls :!: ITbl c t _) vs lu is
    = map (\(S5 s _ _ i o) -> ElmITbl (t ! i) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) lu (tableStreamIndex c vs is)
  {-# INLINE mkStream #-}

