
module ADP.Fusion.Table.Array.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Base



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

