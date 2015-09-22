
-- | Type-level indexing functionality

module ADP.Fusion.Base.TyLvlIx where

import Data.Proxy
import GHC.TypeLits

import Data.PrimitiveArray hiding (map)



-- | Given some complete index list @ixTy@ and some lower-dimensional
-- version @myTy@, walk down along @ixTy@ until we have @is:.i ~ ms:.m@ and
-- return @m@.

class GetIndexGo ixTy myTy (cmp :: Ordering) where
  type ResolvedIx ixTy myTy cmp :: *
  getIndexGo :: ixTy -> (Proxy myTy) -> (Proxy cmp) -> ResolvedIx ixTy myTy cmp

instance GetIndexGo (ix:.i) (my:.m) EQ where
  type ResolvedIx (ix:.i) (my:.m) EQ = i
  getIndexGo (ix:.i) _ _ = i
  {-# Inline getIndexGo #-}

instance (GetIndexGo ix (my:.m) (CmpNat (ToNat ix) (ToNat (my:.m)))) => GetIndexGo (ix:.i) (my:.m) GT where
  type ResolvedIx (ix:.i) (my:.m) GT = ResolvedIx ix (my:.m) (CmpNat (ToNat ix) (ToNat (my:.m)))
  getIndexGo (ix:._) p _ = getIndexGo ix p (Proxy :: Proxy (CmpNat (ToNat ix) (ToNat (my:.m))))
  {-# Inline getIndexGo #-}

instance (GetIndexGo ix Z (CmpNat (ToNat ix) (ToNat Z))) => GetIndexGo (ix:.i) Z GT where
  type ResolvedIx (ix:.i) Z GT = ResolvedIx ix Z (CmpNat (ToNat ix) (ToNat Z))
  getIndexGo (ix:._) p _ = getIndexGo ix p (Proxy :: Proxy (CmpNat (ToNat ix) (ToNat Z)))
  {-# Inline getIndexGo #-}

instance GetIndexGo Z Z EQ where
  type ResolvedIx Z Z EQ = Z
  getIndexGo _ _ _ = Z
  {-# Inline getIndexGo #-}

-- | Wrap @GetIndexGo@ and the type-level shenanigans.

type GetIndex l r = GetIndexGo l r (CmpNat (ToNat l) (ToNat r))

type GetIx l r = ResolvedIx l r (CmpNat (ToNat l) (ToNat r))

-- | Simplifying wrapper around @getIndexGo@.

getIndex
  :: forall ixTy myTy
  .  GetIndex ixTy myTy
  => ixTy
  -> Proxy myTy
  -> GetIx ixTy myTy
getIndex ixTy myTy = getIndexGo ixTy (Proxy :: Proxy myTy) (Proxy :: Proxy (CmpNat (ToNat ixTy) (ToNat myTy)))
{-# Inline getIndex #-}



-- | Given some index structure @x@, return the dimensional number in
-- @Nat@s.

type family ToNat x :: Nat

type instance ToNat Z       = 0
type instance ToNat (is:.i) = ToNat is + 1



{-

testggg :: (Z:.Int:.Char) -> Int
testggg ab = getIndex ab (Proxy :: Proxy (Z:.Int)) --  (Z:.(3::Int))
{-# NoInline testggg #-}

-}

