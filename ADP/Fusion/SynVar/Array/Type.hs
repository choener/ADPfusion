
{-# Language DataKinds #-}
{-# Language TypeOperators #-}

module ADP.Fusion.SynVar.Array.Type where

import Data.Strict.Tuple hiding (uncurry,snd)
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,flatten,Step(..))
import Debug.Trace
import Prelude hiding (map,head,mapM)
import Data.Vector.Fusion.Stream.Size

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Axiom
import ADP.Fusion.SynVar.Indices



-- | Immutable table.

data ITbl m arr i x where
  ITbl :: { iTblBigOrder    :: !Int
          , iTblLittleOrder :: !Int
          , iTblConstraint  :: !(TblConstraint i)
          , iTblArray       :: !(arr i x)
          , iTblFun         :: !(i -> i -> m x)
          } -> ITbl m arr i x

instance Build (ITbl m arr i x)

type instance TermArg (TermSymbol a (ITbl m arr i x)) = TermArg a :. x

instance GenBacktrackTable (ITbl mF arr i x) mF mB r where
  data Backtrack (ITbl mF arr i x) mF mB r = BtITbl !(TblConstraint i) !(arr i x) (i -> i -> mB [r])
  type BacktrackIndex (ITbl mF arr i x) = i
  toBacktrack (ITbl _ _ c arr _) _ bt = BtITbl c arr bt
  {-# Inline toBacktrack #-}

type instance TermArg (TermSymbol a (Backtrack (ITbl mF arr i x) mF mB r)) = TermArg a :. (x,[r])



-- * axiom stuff

instance
  ( Monad m
  , PrimArrayOps arr i x
  , IndexStream i
  ) => Axiom (ITbl m arr i x) where
  type AxiomStream (ITbl m arr i x) = m x
  axiom (ITbl _ _ c arr _) = do
    k <- (head . uncurry streamDown) $ bounds arr
    return $ arr ! k
  {-# Inline axiom #-}

instance
  ( Monad mB
  , PrimArrayOps arr i x
  , IndexStream i
  ) => Axiom (Backtrack (ITbl mF arr i x) mF mB r) where
  type AxiomStream (Backtrack (ITbl mF arr i x) mF mB r) = mB [r]
  axiom (BtITbl c arr bt) = do
    h <- (head . uncurry streamDown) $ bounds arr
    bt (snd $ bounds arr) h
  {-# Inline axiom #-}



-- * 'Element'

instance Element ls i => Element (ls :!: ITbl m arr j x) i where
  data Elm    (ls :!: ITbl m arr j x) i = ElmITbl !x !i !i !(Elm ls i)
  type Arg    (ls :!: ITbl m arr j x)   = Arg ls :. x
  type RecElm (ls :!: ITbl m arr j x) i = Elm ls i
  getArg (ElmITbl x _ _ ls) = getArg ls :. x
  getIdx (ElmITbl _ i _ _ ) = i
  getOmx (ElmITbl _ _ o _ ) = o
  getElm (ElmITbl _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}
  {-# Inline getElm #-}

deriving instance (Show i, Show (Elm ls i), Show x) => Show (Elm (ls :!: ITbl m arr j x) i)

instance Element ls i => Element (ls :!: (Backtrack (ITbl mF arr j x) mF mB r)) i where
  data Elm    (ls :!: (Backtrack (ITbl mF arr j x) mF mB r)) i = ElmBtITbl !x [r] !i !i !(Elm ls i)
  type Arg    (ls :!: (Backtrack (ITbl mF arr j x) mF mB r))   = Arg ls :. (x, [r])
  type RecElm (ls :!: (Backtrack (ITbl mF arr j x) mF mB r)) i = Elm ls i
  getArg (ElmBtITbl x s _ _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtITbl _ _ i _ _ ) = i
  getOmx (ElmBtITbl _ _ _ o _ ) = o
  getElm (ElmBtITbl _ _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}
  {-# Inline getElm #-}

instance (Show x, Show i, Show (Elm ls i)) => Show (Elm (ls :!: (Backtrack (ITbl mF arr i x) mF mB r)) i) where
  show (ElmBtITbl x _ i o s) = show (x,i,o) ++ " " ++ show s



-- * Multi-dim extensions

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , AddIndexDense (is:.i) (is:.i) (is:.i)
  , MkStream m ls (is:.i)
  , PrimArrayOps arr (is:.i) x
  ) => MkStream m (ls :!: ITbl m arr (is:.i) x) (is:.i) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar c vs is) us (tableStreamIndex c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , AddIndexDense (is:.i) (is:.i) (is:.i)
  , MkStream mB ls (is:.i)
  , PrimArrayOps arr (is:.i) x
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr (is:.i) x) mF mB r) (is:.i) where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = mapM (\(s,ii,oo,ii',oo') -> bt us ii >>= \ ~bb -> return $ ElmBtITbl (t!ii) bb ii' oo' s)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar c vs is) us (tableStreamIndex c vs is)
  {-# Inline mkStream #-}

{-
instance
  ( Monad m
  , Element ls (Outside (is:.i))
  , TableStaticVar (Outside (is:.i))
  , TableIndices (Outside (is:.i))
  , MkStream m ls (Outside (is:.i))
  , PrimArrayOps arr (Outside (is:.i)) x
  , Show (is:.i)
  ) => MkStream m (ls :!: ITbl m arr (Outside (is:.i)) x) (Outside (is:.i)) where
  mkStream (ls :!: ITbl _ _ c t _) vs lu is
    = map (\(S5 s _ _ i o) -> ElmITbl (t ! o) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) lu (tableStreamIndex c vs is)
  {-# Inline mkStream #-}
-}

{-
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
    = mapM (\(S5 s _ _ i o) -> bt us o >>= \bb -> return $ ElmBtITbl (t ! o) (bb {-bt us o-}) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) us (tableStreamIndex c vs is)
  {-# Inline mkStream #-}
-}


