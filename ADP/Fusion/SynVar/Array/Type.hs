
{-# Language DataKinds #-}
{-# Language TypeOperators #-}

module ADP.Fusion.SynVar.Array.Type where

import Data.Strict.Tuple hiding (uncurry,snd)
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Debug.Trace
import Prelude hiding (map,head,mapM)
import Data.Proxy

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Axiom
import ADP.Fusion.SynVar.Indices



-- | Immutable table.

data ITbl m arr c i x where
  ITbl :: { iTblBigOrder    :: !Int
          , iTblLittleOrder :: !Int
          , iTblConstraint  :: !c
          , iTblArray       :: !(arr i x)
          , iTblFun         :: !(i -> i -> m x)
          } -> ITbl m arr c i x

instance Build (ITbl m arr c i x)

type instance TermArg (ITbl m arr c i x) = x

instance GenBacktrackTable (ITbl mF arr c i x) mF mB r where
  data Backtrack (ITbl mF arr c i x) mF mB r = BtITbl !c !(arr i x) (i -> i -> mB [r])
  type BacktrackIndex (ITbl mF arr c i x) = i
  toBacktrack (ITbl _ _ c arr _) _ bt = BtITbl c arr bt
  {-# Inline toBacktrack #-}

type instance TermArg (Backtrack (ITbl mF arr c i x) mF mB r) = (x,[r])



-- * axiom stuff

instance
  ( Monad m
  , PrimArrayOps arr i x
  , IndexStream i
  ) => Axiom (ITbl m arr c i x) where
  type AxiomStream (ITbl m arr c i x) = m x
  axiom (ITbl _ _ c arr _) = do
    k <- (head . uncurry streamDown) $ bounds arr
    return $ arr ! k
  {-# Inline axiom #-}

instance
  ( Monad mB
  , PrimArrayOps arr i x
  , IndexStream i
  ) => Axiom (Backtrack (ITbl mF arr c i x) mF mB r) where
  type AxiomStream (Backtrack (ITbl mF arr c i x) mF mB r) = mB [r]
  axiom (BtITbl c arr bt) = do
    h <- (head . uncurry streamDown) $ bounds arr
    bt (snd $ bounds arr) h
  {-# Inline axiom #-}



-- * 'Element'

instance Element ls i => Element (ls :!: ITbl m arr c j x) i where
  data Elm    (ls :!: ITbl m arr c j x) i = ElmITbl !x !(RunningIndex i) !(Elm ls i)
  type Arg    (ls :!: ITbl m arr c j x)   = Arg ls :. x
  type RecElm (ls :!: ITbl m arr c j x) i = Elm ls i
  getArg (ElmITbl x _ ls) = getArg ls :. x
  getIdx (ElmITbl _ i _ ) = i
  getElm (ElmITbl _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i), Show x) => Show (Elm (ls :!: ITbl m arr c j x) i)

instance Element ls i => Element (ls :!: (Backtrack (ITbl mF arr c j x) mF mB r)) i where
  data Elm    (ls :!: (Backtrack (ITbl mF arr c j x) mF mB r)) i = ElmBtITbl !x [r] !(RunningIndex i) !(Elm ls i)
  type Arg    (ls :!: (Backtrack (ITbl mF arr c j x) mF mB r))   = Arg ls :. (x, [r])
  type RecElm (ls :!: (Backtrack (ITbl mF arr c j x) mF mB r)) i = Elm ls i
  getArg (ElmBtITbl x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtITbl _ _ i _ ) = i
  getElm (ElmBtITbl _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

instance (Show x, Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: (Backtrack (ITbl mF arr c i x) mF mB r)) i) where
  show (ElmBtITbl x _ i s) = show (x,i) ++ " " ++ show s



-- * Multi-dim extensions

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (is:.i) (us:.u) (cs:.c) (is:.i)
  , MkStream m ls (is:.i)
  , PrimArrayOps arr (us:.u) x
  ) => MkStream m (ls :!: ITbl m arr (cs:.c) (us:.u) x) (is:.i) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,tt,ii') -> ElmITbl (t!tt) ii' s)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (is:.i) (us:.u) (cs:.c) (is:.i)
  , MkStream mB ls (is:.i)
  , PrimArrayOps arr (us:.u) x
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr (cs:.c) (us:.u) x) mF mB r) (is:.i) where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = mapM (\(s,tt,ii') -> bt us' tt >>= \ ~bb -> return $ ElmBtITbl (t!tt) bb ii' s)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
    where !us' = snd $ bounds t
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


