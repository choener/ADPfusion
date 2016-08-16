
{-# Language MagicHash #-}

module ADP.Fusion.Core.Point where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (singleton,map,filter,Step(..))
import Debug.Trace
import Prelude hiding (map,filter)
import GHC.Exts

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



instance RuleContext (PointL I) where
  type Context (PointL I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

instance RuleContext (PointL O) where
  type Context (PointL O) = OutsideContext Int
  initialContext _ = OStatic 0
  {-# Inline initialContext #-}

instance RuleContext (PointL C) where
  type Context (PointL C) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}

newtype instance RunningIndex (PointL I) = RiPlI Int

data instance RunningIndex (PointL O) = RiPlO !Int !Int

data instance RunningIndex (PointL C) = RiPlC !Int



instance (Monad m) => MkStream m S (PointL I) where
  mkStream S (IStatic (I# d)) (PointL (I# u)) (PointL (I# i))
--    = staticCheck (isTrue# ( (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# d) ) ) -- (i>=0 && i<=d && i<=u)
    = staticCheck# ( (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# d) )
--    = filter (const (isTrue# ( (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# d) ) ))
    . singleton . ElmS $ RiPlI 0
  mkStream S (IVariable _) (PointL (I# u)) (PointL (I# i))
--    = staticCheck (isTrue# ( (i >=# 0#) `andI#` (i <=# u) ) ) -- (i>=0 && i<=u)
    = staticCheck# ( (i >=# 0#) `andI#` (i <=# u) )
--    = filter (const (isTrue# ( (i >=# 0#) `andI#` (i <=# u) ) ))
    . singleton . ElmS $ RiPlI 0
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.PointL I) where
  mkStream S (vs:.IStatic d) (lus:.PointL u) (is:.PointL i)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlI 0)
    . staticCheck (i>=0 && i<=d && i<=u)
    $ mkStream S vs lus is
  mkStream S (vs:.IVariable d) (lus:.PointL u) (is:.PointL i)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlI 0)
    . staticCheck (i>=0 && i<=u)
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}



instance (Monad m) => MkStream m S (PointL O) where
  mkStream S (OStatic d) (PointL u) (PointL i)
    = staticCheck (i>=0 && i+d<=u && u == i) . singleton . ElmS $ RiPlO i (i+d)
  mkStream S (OFirstLeft d) (PointL u) (PointL i)
    = staticCheck (i>=0 && i+d<=u) . singleton . ElmS $ RiPlO i (i+d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.PointL O) where
  mkStream S (vs:.OStatic d) (lus:.PointL u) (is:.PointL i)
    = staticCheck (i>=0 && i+d == u)
    . map (\(ElmS zi) -> ElmS $ zi :.: RiPlO i (i+d))
    $ mkStream S vs lus is
  mkStream S (vs:.OFirstLeft d) (us:.PointL u) (is:.PointL i)
    = staticCheck (i>=0 && i+d<=u)
    . map (\(ElmS zi) -> ElmS $ zi :.: RiPlO i (i+d))
    $ mkStream S vs us is
  {-# Inline mkStream #-}



instance (Monad m) => MkStream m S (PointL C) where
  mkStream S Complemented (PointL u) (PointL i)
    = staticCheck (i>=0 && i<=u) . singleton . ElmS $ RiPlC i
  {-# Inline mkStream #-}



instance (MinSize c) => TableStaticVar u c (PointL I) where
  tableStaticVar _ _ (IStatic   d) _ = IVariable d
  tableStaticVar _ _ (IVariable d) _ = IVariable d
  -- NOTE this code used to destroy fusion. If we inline tableStreamIndex
  -- very late (after 'mkStream', probably) then everything works out.
  tableStreamIndex _ c _ (PointL j) = PointL $ j - minSize c
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance (MinSize c) => TableStaticVar u c (PointL O) where
  tableStaticVar   _ _ (OStatic d) _          = OFirstLeft d
  tableStreamIndex _ c _           (PointL j) = PointL $ j - minSize c
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance (MinSize c) => TableStaticVar u c (PointL C) where
  tableStaticVar   _ _ Complemented _          = Complemented
  tableStreamIndex _ c _            (PointL k) = PointL $ k - minSize c
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

