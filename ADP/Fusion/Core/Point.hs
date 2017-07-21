
{-# Language MagicHash #-}

module ADP.Fusion.Core.Point where

import GHC.Generics (Generic, Generic1)
import Control.DeepSeq
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
  deriving (Generic)

deriving instance NFData (RunningIndex (PointL I))


data instance RunningIndex (PointL O) = RiPlO !Int !Int

newtype instance RunningIndex (PointL C) = RiPlC Int



instance (Monad m) => MkStream m S (PointL I) where
  mkStream grd S (IStatic (I# d)) (PointL (I# u)) (PointL (I# i))
    = staticCheck# ( grd `andI#` (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# u) )
    . singleton . ElmS $ RiPlI 0
  mkStream grd S (IVariable _) (PointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i <=# u) )
    . singleton . ElmS $ RiPlI 0
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.PointL I) where
  mkStream grd S (vs:.IStatic (I# d)) (lus:.PointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS e) -> ElmS $ e :.: RiPlI 0)
    $ mkStream (grd `andI#` (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# u)) S vs lus is
  mkStream grd S (vs:.IVariable d) (lus:.PointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS e) -> ElmS $ e :.: RiPlI 0)
    $ mkStream (grd `andI#` (i >=# 0#) `andI#` (i <=# u)) S vs lus is
  {-# Inline mkStream #-}



instance (Monad m) => MkStream m S (PointL O) where
  mkStream grd S (OStatic (I# d)) (PointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u) `andI#` (u ==# i))
    . singleton . ElmS $ RiPlO (I# i) (I# (i +# d))
  mkStream grd S (OFirstLeft (I# d)) (PointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u))
    . singleton . ElmS $ RiPlO (I# i) (I# (i +# d))
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.PointL O) where
  mkStream grd S (vs:.OStatic (I# d)) (lus:.PointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlO (I# i) (I# (i +# d)))
    $ mkStream (grd `andI#` (i >=# 0#) `andI#` (i +# d ==# u)) S vs lus is
  mkStream grd S (vs:.OFirstLeft (I# d)) (us:.PointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlO (I# i) (I# (i +# d)))
    $ mkStream (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u)) S vs us is
  {-# Inline mkStream #-}



instance (Monad m) => MkStream m S (PointL C) where
  mkStream grd S Complemented (PointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i <=# u)) . singleton . ElmS $ RiPlC (I# i)
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

