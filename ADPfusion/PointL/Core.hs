
{-# Language MagicHash #-}

module ADPfusion.PointL.Core where

import GHC.Generics (Generic, Generic1)
import Control.DeepSeq
import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (singleton,map,filter,Step(..))
import Debug.Trace
import Prelude hiding (map,filter)
import GHC.Exts
import GHC.TypeLits
import Data.Strict.Tuple

import Data.PrimitiveArray hiding (map)

import ADPfusion.Core.Classes
import ADPfusion.Core.Multi
import ADPfusion.Core.SynVar.Split.Type
import ADPfusion.Core.SynVar.Array
import ADPfusion.Core.SynVar.FillTyLvl (IndexConversion(..))



-- * Contexts, and running indices.

type instance InitialContext (PointL I) = IStatic 0

type instance InitialContext (PointL O) = OStatic 0

type instance InitialContext (PointL C) = Complement

newtype instance RunningIndex (PointL I) = RiPlI Int
  deriving Generic
  deriving newtype NFData

data instance RunningIndex (PointL O) = RiPlO !Int !Int
  deriving (Generic)

newtype instance RunningIndex (PointL C) = RiPlC Int
  deriving (Generic)



-- * Inside

-- ** Single-tape
--
-- TODO should IStatic do these additional control of @I <=# d@? cf. Epsilon Local.

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

-- ** Multi-tape

instance
  ( Monad m
  , MkStream m ps S is
  , KnownNat d
  ) ⇒ MkStream m (ps:.IStatic d) S (is:.PointL I) where
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS e) -> ElmS $ e :.: RiPlI 0)
    $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# u)) lus is
    --    $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#)) lus is
    -- NOTE we should optimize which parameters are actually required, the gain is about 10% on the
    -- NeedlemanWunsch algorithm
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
    --    $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#)) lus is
  {-# Inline mkStream #-}



-- * Outside

-- ** Single-tape

instance
  ( Monad m
  , KnownNat d
  ) ⇒ MkStream m (OStatic d) S (PointL O) where
  mkStream Proxy S grd (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i +# d ==# u))
    -- ???  `andI#` (u ==# i)
    . singleton . ElmS $ RiPlO (I# i) (I# (i +# d))
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , KnownNat d
  ) ⇒ MkStream m (OFirstLeft d) S (PointL O) where
  mkStream Proxy s grd (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u))
    . singleton . ElmS $ RiPlO (I# i) (I# (i +# d))
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}

-- ** Multi-tape

instance
  ( Monad m
  , MkStream m ps S is
  , KnownNat d
  ) ⇒ MkStream m (ps:.OStatic d) S (is:.PointL O) where
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlO (I# i) (I# (i +# d)))
    -- ???  `andI#` (u ==# i)
    $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i +# d ==# u)) lus is
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m ps S is
  , KnownNat d
  ) ⇒ MkStream m (ps:.OFirstLeft d) S (is:.PointL O) where
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlO (I# i) (I# (i +# d)))
    $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i +# d <=# u)) lus is
    where (I# d) = fromIntegral $ natVal (Proxy ∷ Proxy d)
  {-# Inline mkStream #-}



-- * Complemented

-- ** Single-tape

instance
  ( Monad m
  ) ⇒ MkStream m Complement S (PointL C) where
  mkStream Proxy S grd (LtPointL (I# u)) (PointL (I# i))
    = error "write me" -- staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i <=# u)) . singleton . ElmS $ RiPlC (I# i)
  {-# Inline mkStream #-}

-- ** Multi-tape

instance
  ( Monad m
  , MkStream m ps S is
  ) ⇒ MkStream m (ps:.Complement) S (is:.PointL C) where
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = error "write me"
    -- -- = map (\(ElmS zi) → ElmS $ zi :.: RiPlC (I# i))
    -- -- $ mkStream (Proxy ∷ Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i <=# u)) lus is
  {-# Inline mkStream #-}



-- * Table index modification

instance (MinSize minSize) ⇒ TableStaticVar pos minSize u (PointL I) where
  -- NOTE this code used to destroy fusion. If we inline tableStreamIndex
  -- very late (after 'mkStream', probably) then everything works out.
  tableStreamIndex Proxy minSz _upperBound (PointL j) = PointL $ j - minSize minSz
  {-# INLINE [0] tableStreamIndex #-}

instance (MinSize minSize) ⇒ TableStaticVar pos minSize u (PointL O) where
  tableStreamIndex Proxy minSz _upperBound (PointL j) = PointL $ j - minSize minSz
  {-# INLINE [0] tableStreamIndex #-}

instance (MinSize minSize) ⇒ TableStaticVar pos minSize u (PointL C) where
  tableStreamIndex Proxy minSz _upperBound (PointL k) = PointL $ k - minSize minSz
  {-# INLINE [0] tableStreamIndex #-}



instance IndexConversion (Z:.PointL ioc:.PointL ioc) (Z:.PointL ioc:.PointL ioc) where
  {-# Inline convertIndex #-}
  convertIndex = Just

instance IndexConversion (Z:.PointL I:.PointL I) (PointL I) where
  {-# Inline convertIndex #-}
  convertIndex (Z:.i:.j)
    | i==j = Just i
    | otherwise = Nothing


-- * Split conversion

instance TermStream m (TermSymbol ts (TwITbl bo so m arr c (PointL I) x)) s (is:.PointL I) bla where
