
module ADP.Fusion.SynVar.Array
  ( module ADP.Fusion.SynVar.Array.Type
  , module ADP.Fusion.SynVar.Array
  ) where


import Data.Proxy
import Data.Strict.Tuple hiding (snd)
import Data.Vector.Fusion.Stream.Monadic
import Prelude hiding (map,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Indices

import ADP.Fusion.SynVar.Array.TermSymbol
import ADP.Fusion.SynVar.Array.Type
import ADP.Fusion.SynVar.TableWrap



-- | Constraints needed to use @iTblStream@.

type ITblCx m ls arr x u c i =
  ( TableStaticVar u c i
  , MkStream m ls i
  , Element ls i
  , AddIndexDense (Elm (SynVar1 (Elm ls i)) (Z:.i)) (Z:.u) (Z:.c) (Z:.i)
  , PrimArrayOps arr u x
  )

-- | General function for @ITbl@s with skalar indices.

iTblStream
  :: forall m ls arr x u c i . ITblCx m ls arr x u c i
  => Pair ls (TwITbl m arr c u x)
  -> Context i
  -> i
  -> i
  -> Stream m (Elm (ls :!: TwITbl m arr c u x) i)
iTblStream (ls :!: TW (ITbl _ _ c t) _) vs us is
  = map (\(s,tt,ii') -> ElmITbl (t!tt) ii' s)
  . addIndexDense1 c vs us is
  $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
{-# Inline iTblStream #-}

-- | General function for @Backtrack ITbl@s with skalar indices.

btITblStream
  :: forall mB mF ls arr x r u c i . ITblCx mB ls arr x u c i
  => Pair ls (TwITblBt arr c u x mF mB r)
  -> Context i
  -> i
  -> i
  -> Stream mB (Elm (ls :!: TwITblBt arr c u x mF mB r) i)
btITblStream (ls :!: TW (BtITbl c t) bt) vs us is
    = mapM (\(s,tt,ii') -> bt us' tt >>= \ ~bb -> return $ ElmBtITbl (t!tt) bb ii' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
    where !us' = snd $ bounds t
{-# Inline btITblStream #-}



-- ** Instances

instance
  ( Monad m
  , ITblCx m ls arr x u c (i I)
  ) => MkStream m (ls :!: TwITbl m arr c u x) (i I) where
  mkStream = iTblStream
  {-# Inline mkStream #-}

instance
  ( Monad m
  , ITblCx m ls arr x u c (i O)
  ) => MkStream m (ls :!: TwITbl m arr c u x) (i O) where
  mkStream = iTblStream
  {-# Inline mkStream #-}

instance
  ( Monad m
  , ITblCx m ls arr x u c (i C)
  ) => MkStream m (ls :!: TwITbl m arr c u x) (i C) where
  mkStream = iTblStream
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , ITblCx mB ls arr x u c (i I)
  ) => MkStream mB (ls :!: TwITblBt arr c u x mF mB r) (i I) where
  mkStream = btITblStream
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , ITblCx mB ls arr x u c (i O)
  ) => MkStream mB (ls :!: TwITblBt arr c u x mF mB r) (i O) where
  mkStream = btITblStream
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , ITblCx mB ls arr x u c (i C)
  ) => MkStream mB (ls :!: TwITblBt arr c u x mF mB r) (i C) where
  mkStream = btITblStream
  {-# Inline mkStream #-}

instance ModifyConstraint (TwITbl m arr EmptyOk i x) where
  type TNE (TwITbl m arr EmptyOk i x) = TwITbl m arr NonEmpty i x
  type TE  (TwITbl m arr EmptyOk i x) = TwITbl m arr EmptyOk  i x
  toNonEmpty (TW (ITbl b l _ arr) f) = TW (ITbl b l NonEmpty arr) f
  {-# Inline toNonEmpty #-}

instance ModifyConstraint (TwITblBt arr EmptyOk i x mF mB r) where
  type TNE (TwITblBt arr EmptyOk i x mF mB r) = TwITblBt arr NonEmpty i x mF mB r
  type TE  (TwITblBt arr EmptyOk i x mF mB r) = TwITblBt arr EmptyOk  i x mF mB r
  toNonEmpty (TW (BtITbl _ arr) bt) = TW (BtITbl NonEmpty arr) bt
  {-# Inline toNonEmpty #-}

