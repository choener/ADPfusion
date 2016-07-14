
{-# Language DataKinds #-}
{-# Language TypeOperators #-}

module ADP.Fusion.SynVar.Array.Type where

import Data.Proxy
import Data.Strict.Tuple hiding (uncurry,snd)
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Debug.Trace
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Axiom
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Indices
import ADP.Fusion.SynVar.TableWrap



-- | Immutable table.

data ITbl arr c i x where
  ITbl :: { iTblBigOrder    :: {-# Unpack #-} !Int
          , iTblLittleOrder :: {-# Unpack #-} !Int
          , iTblConstraint  :: !c
          , iTblArray       :: !(arr i x)
          } -> ITbl arr c i x

type TwITbl m arr c i x = TW m (ITbl arr c i x) x

instance MkTW m (ITbl arr c i x) x where
  data TW m (ITbl arr c i x) x =
    TwITbl
      { twITblMemo :: !(ITbl arr c i x)
      , twITblFun  :: i -> i -> m x
      }
  type TWTblTy m (ITbl arr c i x) x = ITbl arr c i x
  type TWFunTy m (ITbl arr c i x) x = i -> i -> m x
  tw = TwITbl
  {-# Inline tw #-}

type TwITblBt m m' arr c i x r = TW m (Backtrack (TW m' (ITbl arr c i x) x)) r

instance MkTW m (Backtrack (TW m' (ITbl arr c i x) x)) r where
  data TW m (Backtrack (TW m' (ITbl arr c i x) x)) r =
    TwITblBt
      { twBtITbl :: ITbl arr c i x
      , twBtFun  :: i -> i -> m [r]
      }
  type TWTblTy m (Backtrack (TW m' (ITbl arr c i x) x)) r = Backtrack (TwITbl m arr c i x)
  type TWFunTy m (Backtrack (TW m' (ITbl arr c i x) x)) r = i -> i -> m [r]
  tw = \(Backtrack (TwITbl t _)) f -> TwITblBt t f
  {-# Inline tw #-}

instance Build (TW m (ITbl arr c i x) x)

instance Build (TW m (Backtrack (TW m' (ITbl arr c i x) x)) r)

type instance TermArg (TW m (ITbl arr c i x) x) = x

type instance TermArg (TW m (Backtrack (TW m (ITbl arr c i x) x)) r) = (x,[r])



-- * axiom stuff

instance
  ( Monad m
  , PrimArrayOps arr i x
  , IndexStream i
  ) => Axiom (TW m (ITbl arr c i x) x) where
  type AxiomStream (TW m (ITbl arr c i x) x) = m x
  axiom (TwITbl (ITbl _ _ c arr) _) = do
    k <- (head . uncurry streamDown) $ bounds arr
    return $ arr ! k
  {-# Inline axiom #-}

instance
  ( Monad m
  , PrimArrayOps arr i x
  , IndexStream i
  ) => Axiom (TW m (Backtrack (TW m' (ITbl arr c i x) x)) r) where
  type AxiomStream (TW m (Backtrack (TW m' (ITbl arr c i x) x)) r) = m [r]
  axiom (TwITblBt (ITbl _ _ _ arr) bt) = do
    h <- (head . uncurry streamDown) $ bounds arr
    bt (snd $ bounds arr) h
  {-# Inline axiom #-}

{-
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
-}

-- * 'Element'

instance Element ls i => Element (ls :!: TW m (ITbl arr c j x) x) i where
  data Elm    (ls :!: TW m (ITbl arr c j x) x) i = ElmITbl !x !(RunningIndex i) !(Elm ls i)
  type Arg    (ls :!: TW m (ITbl arr c j x) x)   = Arg ls :. x
  type RecElm (ls :!: TW m (ITbl arr c j x) x) i = Elm ls i
  getArg (ElmITbl x _ ls) = getArg ls :. x
  getIdx (ElmITbl _ i _ ) = i
  getElm (ElmITbl _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i), Show x) => Show (Elm (ls :!: TW m (ITbl arr c j x) x) i)

instance Element ls i => Element (ls :!: TW m (Backtrack (TW m' (ITbl arr c j x) x)) r) i where
  data Elm    (ls :!: TW m (Backtrack (TW m' (ITbl arr c j x) x)) r) i = ElmBtITbl !x [r] !(RunningIndex i) !(Elm ls i)
  type Arg    (ls :!: TW m (Backtrack (TW m' (ITbl arr c j x) x)) r)   = Arg ls :. (x, [r])
  type RecElm (ls :!: TW m (Backtrack (TW m' (ITbl arr c j x) x)) r) i = Elm ls i
  getArg (ElmBtITbl x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtITbl _ _ i _ ) = i
  getElm (ElmBtITbl _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

--instance (Show x, Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: TwITblBt arr c i x mF mB r) i) where
--  show (ElmBtITbl x _ i s) = show (x,i) ++ " " ++ show s

-- * Multi-dim extensions

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (Elm ls (is:.i)) (us:.u) (cs:.c) (is:.i)
  , MkStream m ls (is:.i)
  , PrimArrayOps arr (us:.u) x
  ) => MkStream m (ls :!: TW m (ITbl arr (cs:.c) (us:.u) x) x) (is:.i) where
  mkStream (ls :!: TwITbl (ITbl _ _ c t) _) vs us is
    = map (\(s,tt,ii') -> ElmITbl (t!tt) ii' s)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (Elm ls (is:.i)) (us:.u) (cs:.c) (is:.i)
  , MkStream m ls (is:.i)
  , PrimArrayOps arr (us:.u) x
  ) => MkStream m (ls :!: TW m (Backtrack (TW m' (ITbl arr (cs:.c) (us:.u) x) x)) r) (is:.i) where
  mkStream (ls :!: TwITblBt (ITbl _ _ c t) bt) vs us is
    = mapM (\(s,tt,ii') -> bt us' tt >>= \ ~bb -> return $ ElmBtITbl (t!tt) bb ii' s)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
    where !us' = snd $ bounds t
  {-# Inline mkStream #-}

