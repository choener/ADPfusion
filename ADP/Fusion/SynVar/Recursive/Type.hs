
module ADP.Fusion.SynVar.Recursive.Type where

import Data.Strict.Tuple ((:!:)(..))
import Data.Vector.Fusion.Stream.Monadic (Stream,head)
import Prelude hiding (head)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Axiom



data IRec m i x where
  IRec :: { iRecConstraint  :: !(TblConstraint i)
          , iRecFrom        :: !i
          , iRecTo          :: !i
          , iRecFun         :: !(i -> i -> m x)
          } -> IRec m i x



instance Build (IRec m i x)

instance GenBacktrackTable (IRec mF i x) mF mB r where
  data Backtrack (IRec mF i x) mF mB r = BtIRec !(TblConstraint i) !i !i (i -> i -> mB x) (i -> i -> mB (Stream mB r))
  type BacktrackIndex (IRec mF i x)         = i
  toBacktrack (IRec c iF iT f) mrph bt = BtIRec c iF iT (\lu i -> mrph $ f lu i) bt
  {-# INLINE toBacktrack #-}



instance
  ( Monad m
  , IndexStream i
  ) => Axiom (IRec m i x) where
  type AxiomStream (IRec m i x) = m x
  axiom (IRec c l h fun) = do
    k <- (head . uncurry streamDown) (l,h)
    fun h k
  {-# Inline axiom #-}

instance
  ( Monad mB
  , IndexStream i
  ) => Axiom (Backtrack (IRec mF i x) mF mB r) where
  type AxiomStream (Backtrack (IRec mF i x) mF mB r) = mB (Stream mB r)
  axiom (BtIRec c l h fun btfun) = do
    k <- (head . uncurry streamDown) (l,h)
    btfun h k
  {-# Inline axiom #-}



instance Element ls i => Element (ls :!: IRec m i x) i where
  data Elm (ls :!: IRec m i x) i = ElmIRec !x !i !i !(Elm ls i)
  type Arg (ls :!: IRec m i x)   = Arg ls :. x
  getArg (ElmIRec x _ _ ls) = getArg ls :. x
  getIdx (ElmIRec _ i _ _ ) = i
  getOmx (ElmIRec _ _ o _ ) = o
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}

instance Element ls i => Element (ls :!: (Backtrack (IRec mF i x) mF mB r)) i where
  data Elm (ls :!: (Backtrack (IRec mF i x) mF mB r)) i = ElmBtIRec !x !(mB (Stream mB r)) !i !i !(Elm ls i)
  type Arg (ls :!: (Backtrack (IRec mF i x) mF mB r))   = Arg ls :. (x, mB (Stream mB r))
  getArg (ElmBtIRec x s _ _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtIRec _ _ i _ _ ) = i
  getOmx (ElmBtIRec _ _ _ o _ ) = o
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}



-- TODO write multi-tape instances

