
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

-- | The pair of Nats encodes the minimal maximal "enlargement" of the non-terminal on the rhs. A
-- 'Chr', for example enlarges by @1@, while a 'Str' enlarges by @(0.., 0..unbounded)@

type instance InitialContext (PointL O) = OStatic '(0,0)

type instance InitialContext (PointL C) = Complement

-- | The running index for @PointL I@ is simple: just store the current intermediate index. Given a
-- rule @X_0j -> X_0k t_kj@ we only need the @k@ and @j@ indices. For *terminals* only, it is
-- allowing to parse variable-length symbols.

newtype instance RunningIndex (PointL I) = RiPlI Int
  deriving Generic
  deriving newtype NFData

-- | @RiPlO k l@ holds a moving outside index.
--
-- Outside indices have to deal with some cases. Consider these rules in inside form first, then
-- outside.
-- @
-- Static:
-- X_j     -> X_(j-1) t_j
-- X_(j-1) -> X_j t_j   rewrite to
-- X_j     -> X_(j+1) t_(j+1)
--
-- X_0j     -> X_0(j-2) s_(j-1) t_j
-- X_0(j-2) -> x_0j s_(j-1) t_j   rewrite to
-- X_0j     -> x_0(j+2) s_(j+1) t_(j+2)
--
-- Variable:
-- X_0j -> X_0k t_kj
-- X_0k -> X_0j t_kj   rewrite to
-- X_0j -> x_0k t_jk   with j<=k
--
-- X_0j -> X_0k s_kl t_lj
-- X_0k -> X_0j s_kl t_lj   rewrite to
-- X_0j -> X_0k s_jl t_lk   with j<=l<=k
-- [....j...] -> [....j.l.k.]
-- @
--
-- @RiPlO ix (ix+d)@ means that @ix@ holds the actual index on the lhs, while @ix+d@ is the maximal
-- amount of difference, ie. @j-k@ we allow.
--
-- NOTE I think a single index is enough, given that we now track minima,maxima via type-level
-- constructions.
--
-- TODO one index is not enough, the case of two var-lenght terminals requires tracking both types
-- of indices separably

data instance RunningIndex (PointL O) = RiPlO { synvarIndex :: !Int, terminalIndex :: !Int }
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
  => MkStream m (IStatic d) S (PointL I) where
  mkStream Proxy S grd (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# ( grd `andI#` (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# u) )
    . singleton . ElmS $ RiPlI 0
    where (I# d) = fromIntegral $ natVal (Proxy :: Proxy d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , KnownNat d
  )
  => MkStream m (IVariable d) S (PointL I) where
  mkStream Proxy S grd (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i <=# u) )
    . singleton . ElmS $ RiPlI 0
  {-# Inline mkStream #-}

-- ** Multi-tape

instance
  ( Monad m
  , MkStream m ps S is
  , KnownNat d
  ) => MkStream m (ps:.IStatic d) S (is:.PointL I) where
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS e) -> ElmS $ e :.: RiPlI 0)
    $ mkStream (Proxy :: Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i <=# d) `andI#` (i <=# u)) lus is
    --    $ mkStream (Proxy :: Proxy ps) S (grd `andI#` (i >=# 0#)) lus is
    -- NOTE we should optimize which parameters are actually required, the gain is about 10% on the
    -- NeedlemanWunsch algorithm
    where (I# d) = fromIntegral $ natVal (Proxy :: Proxy d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m ps S is
  , KnownNat d
  ) => MkStream m (ps:.IVariable d) S (is:.PointL I) where
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS e) -> ElmS $ e :.: RiPlI 0)
    $ mkStream (Proxy :: Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i <=# u)) lus is
    --    $ mkStream (Proxy :: Proxy ps) S (grd `andI#` (i >=# 0#)) lus is
  {-# Inline mkStream #-}



-- * Outside

-- ** Single-tape

-- |
--
-- NOTE I am not checking that @low==high@. Any terminal that writes an instance should guarantee
-- this!
--
-- TODO Consider if we can just assert low==high in the instance header.

instance (Monad m, KnownNat low, KnownNat high) => MkStream m (OStatic '(low,high)) S (PointL O) where
--{{{
  {-# Inline mkStream #-}
  mkStream Proxy S grd (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i +# high ==# u))
    . singleton . ElmS $ RiPlO (I# i) (I# i)
    where
     (I# low) = fromIntegral $ natVal (Proxy @low)
     (I# high) = fromIntegral $ natVal (Proxy @high)
--}}}

instance ( Monad m, KnownNat low, KnownNat high) => MkStream m (OFirstLeft '(low,high)) S (PointL O) where
--{{{
  {-# Inline mkStream #-}
  mkStream Proxy s grd (LtPointL (I# u)) (PointL (I# i))
    = staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i +# low <=# u))
    . singleton . ElmS $ RiPlO (I# i) (I# i)
    where
     (I# low) = fromIntegral $ natVal (Proxy @low)
     (I# high) = fromIntegral $ natVal (Proxy @high)
--}}}

-- ** Multi-tape

instance
  ( Monad m, MkStream m ps S is, KnownNat low, KnownNat high
  ) => MkStream m (ps:.OStatic '(low,high)) S (is:.PointL O) where
--{{{
  {-# Inline mkStream #-}
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlO (I# i) (I# i))
    $ mkStream (Proxy :: Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i +# low ==# u)) lus is
    where
     (I# low) = fromIntegral $ natVal (Proxy @low)
     (I# high) = fromIntegral $ natVal (Proxy @high)
--}}}

instance
  ( Monad m, MkStream m ps S is, KnownNat low, KnownNat high
  ) => MkStream m (ps:.OFirstLeft '(low,high)) S (is:.PointL O) where
--{{{
  {-# Inline mkStream #-}
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = map (\(ElmS zi) -> ElmS $ zi :.: RiPlO (I# i) (I# i))
    $ mkStream (Proxy :: Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i +# low <=# u)) lus is
    where
     (I# low) = fromIntegral $ natVal (Proxy @low)
     (I# high) = fromIntegral $ natVal (Proxy @high)
--}}}


-- * Complemented

-- ** Single-tape

instance
  ( Monad m
  ) => MkStream m Complement S (PointL C) where
  mkStream Proxy S grd (LtPointL (I# u)) (PointL (I# i))
    = error "write me" -- staticCheck# (grd `andI#` (i >=# 0#) `andI#` (i <=# u)) . singleton . ElmS $ RiPlC (I# i)
  {-# Inline mkStream #-}

-- ** Multi-tape

instance
  ( Monad m
  , MkStream m ps S is
  ) => MkStream m (ps:.Complement) S (is:.PointL C) where
  mkStream Proxy S grd (lus:..LtPointL (I# u)) (is:.PointL (I# i))
    = error "write me"
    -- -- = map (\(ElmS zi) → ElmS $ zi :.: RiPlC (I# i))
    -- -- $ mkStream (Proxy :: Proxy ps) S (grd `andI#` (i >=# 0#) `andI#` (i <=# u)) lus is
  {-# Inline mkStream #-}



-- * Table index modification

instance (MinSize minSize) => TableStaticVar pos minSize u (PointL I) where
  -- NOTE this code used to destroy fusion. If we inline tableStreamIndex
  -- very late (after 'mkStream', probably) then everything works out.
  tableStreamIndex Proxy minSz _upperBound (PointL j) = PointL $ j - minSize minSz
  {-# INLINE [0] tableStreamIndex #-}

instance (MinSize minSize) => TableStaticVar pos minSize u (PointL O) where
  tableStreamIndex Proxy minSz _upperBound (PointL j) = PointL $ j - minSize minSz
  {-# INLINE [0] tableStreamIndex #-}

instance (MinSize minSize) => TableStaticVar pos minSize u (PointL C) where
  tableStreamIndex Proxy minSz _upperBound (PointL k) = PointL $ k - minSize minSz
  {-# INLINE [0] tableStreamIndex #-}



instance IndexConversion (Z:.PointL ioc:.PointL ioc) (Z:.PointL ioc:.PointL ioc) where
--{{{
  {-# Inline convertIndex #-}
  convertIndex = Just
--}}}

instance IndexConversion (Z:.PointL I:.PointL I) (PointL I) where
--{{{
  {-# Inline convertIndex #-}
  convertIndex (Z:.i:.j)
    | i==j = Just i
    | otherwise = Nothing
--}}}

instance IndexConversion (Z:.PointL I) (Z:.PointL I) where
--{{{
  {-# Inline convertIndex #-}
  convertIndex = Just
--}}}

instance IndexConversion (PointL I) (PointL I) where
--{{{
  {-# Inline convertIndex #-}
  convertIndex = Just
--}}}

-- * Split conversion

instance TermStream m (TermSymbol ts (TwITbl bo so m arr c (PointL I) x)) s (is:.PointL I) bla where
