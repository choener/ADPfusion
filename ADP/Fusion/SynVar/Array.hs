
{-# Language MagicHash #-}

module ADP.Fusion.SynVar.Array
  ( module ADP.Fusion.SynVar.Array.Type
  , module ADP.Fusion.SynVar.Array
  ) where


import Data.Proxy
import Data.Strict.Tuple hiding (snd)
import Data.Vector.Fusion.Stream.Monadic
import GHC.Exts
import Prelude hiding (map,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi
import ADP.Fusion.SynVar.Array.Type
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Indices.Classes
import ADP.Fusion.SynVar.TableWrap



-- | Constraints needed to use @iTblStream@.

type ITblCx m pos ls arr x u c i =
  ( TableStaticVar pos c u i
  , Element ls i
  , AddIndexDense (Z:.pos) (Elm (SynVar1 (Elm ls i)) (Z:.i)) (Z:.c) (Z:.u) (Z:.i)
  , PrimArrayOps arr u x
  )

-- | General function for @ITbl@s with skalar indices.

iTblStream
  ∷ forall m pos posLeft ls arr x u c i
  . ( ITblCx m pos ls arr x u c i
    , posLeft ~ LeftPosTy pos (TwITbl m arr c u x) i
    , MkStream m posLeft ls i
    )
  ⇒ Proxy pos
  → Pair ls (TwITbl m arr c u x)
  → Int#
  → LimitType i
  → i
  → Stream m (Elm (ls :!: TwITbl m arr c u x) i)
iTblStream pos (ls :!: TW (ITbl _ _ c t) _) grd us is
  = map (\(s,tt,ii') -> ElmITbl (t!tt) ii' s)
  . addIndexDense1 pos c ub us is
  $ mkStream (Proxy ∷ Proxy posLeft) ls grd us (tableStreamIndex (Proxy :: Proxy pos) c ub is)
  where ub = upperBound t
{-# Inline iTblStream #-}

-- | General function for @Backtrack ITbl@s with skalar indices.

btITblStream
  ∷ forall mB mF pos posLeft ls arr x r u c i
  . ( ITblCx mB pos ls arr x u c i
    , posLeft ~ LeftPosTy pos (TwITblBt arr c u x mF mB r) i
    , MkStream mB posLeft ls i
    )
  ⇒ Proxy pos
  → Pair ls (TwITblBt arr c u x mF mB r)
  → Int#
  → LimitType i
  → i
  → Stream mB (Elm (ls :!: TwITblBt arr c u x mF mB r) i)
btITblStream pos (ls :!: TW (BtITbl c t) bt) grd us is
    = mapM (\(s,tt,ii') -> bt ub tt >>= \ ~bb -> return $ ElmBtITbl (t!tt) bb ii' s)
    . addIndexDense1 pos c ub us is
    $ mkStream (Proxy ∷ Proxy posLeft) ls grd us (tableStreamIndex (Proxy :: Proxy pos) c ub is)
    where ub = upperBound t
{-# Inline btITblStream #-}



-- ** Instances

type instance LeftPosTy (IStatic d) (TwITbl m arr EmptyOk (PointL I) x) (PointL I) = IVariable d
type instance LeftPosTy (IStatic d) (TwITblBt arr EmptyOk (PointL I) x mB mF r) (PointL I) = IVariable d

instance
  ( Monad m
  , ITblCx m pos ls arr x u c (i I)
  , MkStream m (LeftPosTy pos (TwITbl m arr c u x) (i I)) ls (i I)
  ) => MkStream m pos (ls :!: TwITbl m arr c u x) (i I) where
  mkStream = iTblStream
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , ITblCx mB pos ls arr x u c (i I)
  , MkStream mB (LeftPosTy pos (TwITblBt arr c u x mF mB r) (i I)) ls (i I)
  )
  ⇒ MkStream mB pos (ls :!: TwITblBt arr c u x mF mB r) (i I) where
  mkStream = btITblStream
  {-# Inline mkStream #-}

{-
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
-}

