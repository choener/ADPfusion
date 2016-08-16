
{-# Language DataKinds #-}
{-# Language TypeOperators #-}

module ADP.Fusion.SynVar.Array.Type where

import Data.Proxy
import Data.Strict.Tuple hiding (uncurry,snd)
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Debug.Trace
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi
import ADP.Fusion.SynVar.Axiom
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Indices.Classes
import ADP.Fusion.SynVar.TableWrap



-- | Immutable table.

data ITbl arr c i x where
  ITbl :: { iTblBigOrder    :: {-# Unpack #-} !Int
          , iTblLittleOrder :: {-# Unpack #-} !Int
          , iTblConstraint  :: !c
          , iTblArray       :: !(arr i x)
          } -> ITbl arr c i x

type TwITbl m arr c i x = TW (ITbl arr c i x) (i -> i -> m x)

type TwITblBt arr c i x mF mB r = TW (Backtrack (TwITbl mF arr c i x) mF mB) (i -> i -> mB [r])

instance Build (TwITbl m arr c i x)

instance Build (TwITblBt arr c i x mF mB r)

type instance TermArg (TwITbl m arr c i x) = x

instance GenBacktrackTable (TwITbl mF arr c i x) mF mB where
  data Backtrack (TwITbl mF arr c i x) mF mB = BtITbl !c !(arr i x) -- !(i -> i -> mB [r])
  type BacktrackIndex (TwITbl mF arr c i x) = i
  toBacktrack (TW (ITbl _ _ c arr) _) _ = BtITbl c arr
  {-# Inline toBacktrack #-}

type instance TermArg (TwITblBt arr c i x mF mB r) = (x,[r])



-- * axiom stuff

instance
  ( Monad m
  , PrimArrayOps arr i x
  , IndexStream i
  ) => Axiom (TwITbl m arr c i x) where
  type AxiomStream (TwITbl m arr c i x) = m x
  axiom (TW (ITbl _ _ c arr) _) = do
    k <- (head . uncurry streamDown) $ bounds arr
    return $ arr ! k
  {-# Inline axiom #-}

-- | We need this somewhat annoying instance construction (@i ~ j@ and @m
-- ~ mB@) in order to force selection of this instance.

instance
  ( Monad mB
  , PrimArrayOps arr i x
  , IndexStream i
  , j ~ i
  , m ~ mB
  ) => Axiom (TW (Backtrack (TwITbl mF arr c i x) mF mB) (j -> j -> m [r])) where
  type AxiomStream (TW (Backtrack (TwITbl mF arr c i x) mF mB) (j -> j -> m [r])) = mB [r]
  axiom (TW (BtITbl c arr) bt) = do
    h <- (head . uncurry streamDown) $ bounds arr
    bt (snd $ bounds arr) h
  {-# Inline axiom #-}



-- * 'Element'

instance Element ls i => Element (ls :!: TwITbl m arr c j x) i where
  data Elm    (ls :!: TwITbl m arr c j x) i = ElmITbl !x !(RunningIndex i) !(Elm ls i)
  type Arg    (ls :!: TwITbl m arr c j x)   = Arg ls :. x
  type RecElm (ls :!: TwITbl m arr c j x) i = Elm ls i
  getArg (ElmITbl x _ ls) = getArg ls :. x
  getIdx (ElmITbl _ i _ ) = i
  getElm (ElmITbl _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i), Show x) => Show (Elm (ls :!: TwITbl m arr c j x) i)

instance Element ls i => Element (ls :!: TwITblBt arr c j x mF mB r) i where
  data Elm    (ls :!: TwITblBt arr c j x mF mB r) i = ElmBtITbl !x [r] !(RunningIndex i) !(Elm ls i)
  type Arg    (ls :!: TwITblBt arr c j x mF mB r)   = Arg ls :. (x, [r])
  type RecElm (ls :!: TwITblBt arr c j x mF mB r) i = Elm ls i
  getArg (ElmBtITbl x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtITbl _ _ i _ ) = i
  getElm (ElmBtITbl _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

instance (Show x, Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: TwITblBt arr c i x mF mB r) i) where
  show (ElmBtITbl x _ i s) = show (x,i) ++ " " ++ show s



-- * Multi-dim extensions

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (Elm ls (is:.i)) (us:.u) (cs:.c) (is:.i)
  , MkStream m ls (is:.i)
  , PrimArrayOps arr (us:.u) x
  ) => MkStream m (ls :!: TwITbl m arr (cs:.c) (us:.u) x) (is:.i) where
  mkStream (ls :!: TW (ITbl _ _ c t) _) vs us is
    = map (\(s,tt,ii') -> ElmITbl (t!tt) ii' s)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (Elm ls (is:.i)) (us:.u) (cs:.c) (is:.i)
  , MkStream mB ls (is:.i)
  , PrimArrayOps arr (us:.u) x
  ) => MkStream mB (ls :!: TwITblBt arr (cs:.c) (us:.u) x mF mB r) (is:.i) where
  mkStream (ls :!: TW (BtITbl c t) bt) vs us is
    = mapM (\(s,tt,ii') -> bt us' tt >>= \ ~bb -> return $ ElmBtITbl (t!tt) bb ii' s)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
    where !us' = snd $ bounds t
  {-# Inline mkStream #-}

