
{-# Language MagicHash #-}

module ADPfusion.PointR.Core where

import GHC.Generics (Generic, Generic1)
import Control.DeepSeq
import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (singleton,map,filter,Step(..))
import Debug.Trace
import Prelude hiding (map,filter)
import GHC.Exts
import GHC.TypeLits

import Data.PrimitiveArray hiding (map)

import ADPfusion.Core.Classes
import ADPfusion.Core.Multi



-- * Contexts, and running indices.

type instance InitialContext (PointR I) = IStatic 0

type instance InitialContext (PointR O) = OStatic 0

type instance InitialContext (PointR C) = Complement

newtype instance RunningIndex (PointR I) = RiPrI Int
  deriving Generic
  deriving newtype NFData

data instance RunningIndex (PointR O) = RiPrO !Int !Int
  deriving (Generic)

newtype instance RunningIndex (PointR C) = RiPrC Int
  deriving (Generic)



-- * Inside

-- ** Single-tape

instance
  ( Monad m
  , KnownNat d
  )
  ⇒ MkStream m (IStatic d) S (PointR I) where
  mkStream Proxy S grd (LtPointR (I# u)) (PointR (I# i))
    = staticCheck# ( grd `andI#` (i >=# 0#) `andI#` (i +# d ==# u) )   -- TODO include @d@ correctly: i<=d
    . singleton . ElmS . RiPrI $ I# i
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , KnownNat d
  )
  ⇒ MkStream m (IVariable d) S (PointR I) where
  mkStream Proxy S grd (LtPointR (I# u)) (PointR (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u))
    . singleton . ElmS . RiPrI $ I# i
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}



-- ** Multi-tape

instance
  ( Monad m
  , MkStream m ps S is
  , KnownNat d
  ) ⇒ MkStream m (ps:.IStatic d) S (is:.PointR I) where
  mkStream Proxy S grd (lus:..LtPointR (I# u)) (is:.PointR (I# i))
    = map (\(ElmS e) -> ElmS $ e :.: RiPrI (I# i))
    $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i +# d ==# u)) lus is
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m ps S is
  , KnownNat d
  ) ⇒ MkStream m (ps:.IVariable d) S (is:.PointR I) where
  mkStream Proxy S grd (lus:..LtPointR (I# u)) (is:.PointR (I# i))
    = map (\(ElmS e) -> ElmS $ e :.: RiPrI (I# i))
    $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u)) lus is
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}



-- * Outside

-- ** Single-tape




-- * Complemented

-- ** Single-tape


-- ** Multi-tape




-- * Table index modification

instance (MinSize minSize) ⇒ TableStaticVar pos minSize u (PointR I) where
  -- NOTE this code used to destroy fusion. If we inline tableStreamIndex
  -- very late (after 'mkStream', probably) then everything works out.
  tableStreamIndex Proxy minSz _upperBound (PointR j) = PointR $ j + minSize minSz
  {-# INLINE [0] tableStreamIndex #-}

