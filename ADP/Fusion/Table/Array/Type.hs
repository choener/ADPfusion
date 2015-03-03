
module ADP.Fusion.Table.Array.Type where

import Data.Strict.Tuple hiding (uncurry,snd)
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head)
import Debug.Trace
import Prelude hiding (map,head)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.Table.Backtrack
import ADP.Fusion.Table.Axiom
import ADP.Fusion.Table.Indices



-- | Immutable table.

data ITbl m arr i x where
  ITbl :: { iTblConstraint :: !(TblConstraint i)
          , iTblArray      :: !(arr i x)
          , iTblFun        :: !(i -> i -> m x)
          } -> ITbl m arr i x

instance Build (ITbl m arr i x)

instance GenBacktrackTable (ITbl mF arr i x) mF mB r where
  data Backtrack (ITbl mF arr i x) mF mB r = BtITbl !(TblConstraint i) !(arr i x) (i -> i -> mB (Stream mB r))
  type BacktrackIndex (ITbl mF arr i x) = i
  toBacktrack (ITbl c arr _) _ bt = BtITbl c arr bt
  {-# Inline toBacktrack #-}

instance (Show i, PrimArrayOps arr i x, Monad mB, IndexStream i) => Axiom (Backtrack (ITbl mF arr i x) mF mB r) where
  type AxiomStream (Backtrack (ITbl mF arr i x) mF mB r) = mB (Stream mB r)
  axiom (BtITbl c arr bt) = do
    h <- (head . uncurry streamDown) $ bounds arr
    bt (snd $ bounds arr) h
  {-# Inline axiom #-}

instance Element ls i => Element (ls :!: ITbl m arr j x) i where
  data Elm (ls :!: ITbl m arr j x) i = ElmITbl !x !i !i !(Elm ls i)
  type Arg (ls :!: ITbl m arr j x)   = Arg ls :. x
  getArg (ElmITbl x _ _ ls) = getArg ls :. x
  getIdx (ElmITbl _ i _ _ ) = i
  getOmx (ElmITbl _ _ o _ ) = o
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}

deriving instance (Show i, Show (Elm ls i), Show x) => Show (Elm (ls :!: ITbl m arr j x) i)

instance Element ls i => Element (ls :!: (Backtrack (ITbl mF arr i x) mF mB r)) i where
  data Elm (ls :!: (Backtrack (ITbl mF arr i x) mF mB r)) i = ElmBtITbl !x !(mB (Stream mB r)) !i !i !(Elm ls i)
  type Arg (ls :!: (Backtrack (ITbl mF arr i x) mF mB r))   = Arg ls :. (x, mB (Stream mB r))
  getArg (ElmBtITbl x s _ _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtITbl _ _ i _ _ ) = i
  getOmx (ElmBtITbl _ _ _ o _ ) = o
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}

instance (Show x, Show i, Show (Elm ls i)) => Show (Elm (ls :!: (Backtrack (ITbl mF arr i x) mF mB r)) i) where
  show (ElmBtITbl x _ i o s) = show (x,i,o) ++ " " ++ show s

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
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , MkStream mB ls (is:.i)
  , PrimArrayOps arr (is:.i) x
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr (is:.i) x) mF mB r) (is:.i) where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = map (\(S5 s _ _ i o) -> ElmBtITbl (t ! i) (bt us i) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) us (tableStreamIndex c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Outside (is:.i))
  , TableStaticVar (Outside (is:.i))
  , TableIndices (Outside (is:.i))
  , MkStream m ls (Outside (is:.i))
  , PrimArrayOps arr (Outside (is:.i)) x
  , Show (is:.i)
  ) => MkStream m (ls :!: ITbl m arr (Outside (is:.i)) x) (Outside (is:.i)) where
  mkStream (ls :!: ITbl c t _) vs lu is
    = map (\(S5 s _ _ i o) -> ElmITbl (t ! o) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) lu (tableStreamIndex c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (Outside (is:.i))
  , TableStaticVar (Outside (is:.i))
  , TableIndices (Outside (is:.i))
  , MkStream mB ls (Outside (is:.i))
  , PrimArrayOps arr (Outside (is:.i)) x
  , Show (is:.i)
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr (Outside (is:.i)) x) mF mB r) (Outside (is:.i)) where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = map (\(S5 s _ _ i o) -> ElmBtITbl (t ! o) (bt us o) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) us (tableStreamIndex c vs is)
  {-# Inline mkStream #-}

