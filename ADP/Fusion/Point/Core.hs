
{-# Language MagicHash #-}

module ADP.Fusion.Point.Core where

import GHC.Generics (Generic, Generic1)
import Control.DeepSeq
import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (singleton,map,filter,Step(..))
import Debug.Trace
import Prelude hiding (map,filter)
import GHC.Exts
import GHC.TypeLits

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



--instance RuleContext (PointL I) where
type instance InitialContext (PointL I) = IStatic 0

--instance RuleContext (PointL O) where
type instance InitialContext (PointL O) = OStatic 0

--instance RuleContext (PointL C) where
type instance InitialContext (PointL C) = Complement

newtype instance RunningIndex (PointL I) = RiPlI Int
  deriving (Generic)

deriving instance NFData (RunningIndex (PointL I))


data instance RunningIndex (PointL O) = RiPlO !Int !Int

newtype instance RunningIndex (PointL C) = RiPlC Int



instance
  ( Monad m
  , KnownNat d
  )
  ⇒ MkStream m (IStatic d) S (PointL I) where
  mkStream Proxy S grd (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# ( grd `andI#` (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# u) )
    . singleton . ElmS $ RiPlI 0
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , KnownNat d
  )
  ⇒ MkStream m (IVariable d) S (PointL I) where
  mkStream Proxy S grd (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i <=# u) )
    . singleton . ElmS $ RiPlI 0
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m ps S is
  , KnownNat d
  ) ⇒ MkStream m (ps:.IStatic d) S (is:.PointL I) where
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS e) -> ElmS $ e :.: RiPlI 0)
    $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# u)) lus is
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m ps S is
  , KnownNat d
  ) ⇒ MkStream m (ps:.IVariable d) S (is:.PointL I) where
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS e) -> ElmS $ e :.: RiPlI 0)
    $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i <=# u)) lus is
  {-# Inline mkStream #-}



{-
instance (Monad m) => MkStream m S (PointL O) where
  mkStream grd S (OStatic (I# d)) (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u) `andI#` (u ==# i))
    . singleton . ElmS $ RiPlO (I# i) (I# (i +# d))
  mkStream grd S (OFirstLeft (I# d)) (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u))
    . singleton . ElmS $ RiPlO (I# i) (I# (i +# d))
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.PointL O) where
  mkStream grd S (vs:.OStatic (I# d)) (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlO (I# i) (I# (i +# d)))
    $ mkStream (grd `andI#` (i >=# 0#) `andI#` (i +# d ==# u)) S vs lus is
  mkStream grd S (vs:.OFirstLeft (I# d)) (us:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlO (I# i) (I# (i +# d)))
    $ mkStream (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u)) S vs us is
  {-# Inline mkStream #-}



instance (Monad m) => MkStream m S (PointL C) where
  mkStream grd S Complemented (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i <=# u)) . singleton . ElmS $ RiPlC (I# i)
  {-# Inline mkStream #-}
-}


instance (MinSize minSize) => TableStaticVar pos minSize u (PointL I) where
  -- NOTE this code used to destroy fusion. If we inline tableStreamIndex
  -- very late (after 'mkStream', probably) then everything works out.
  tableStreamIndex Proxy minSz _ (PointL j) = PointL $ j - minSize minSz
  {-# INLINE [0] tableStreamIndex #-}

{-
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
-}

