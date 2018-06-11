
-- |
--
-- TODO Need to add additional type family instances as required.
--
-- TODO Need to have little order nats as well.

module ADP.Fusion.Core.SynVar.FillTyLvl where

import           Control.Monad.ST
import           Control.Monad.Primitive
import           Data.Promotion.Prelude.Bool
import           Data.Promotion.Prelude.List
import           Data.Proxy
import           Data.Singletons.Prelude.Bool
import           Data.Type.Equality
import           GHC.Exts
import           GHC.TypeNats
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           Data.Vector.Fusion.Util (Id(..))

import           Data.PrimitiveArray

import           ADP.Fusion.Core.SynVar.TableWrap
import           ADP.Fusion.Core.SynVar.Array



-- | Fill/mutate tables using @ST@.

fillTablesST
  ∷ forall bigOrder ts
  . ( bigOrder ~ BigOrderNats ts
    , EachBigOrder bigOrder ts
    )
  ⇒ ts
  → ts
{-# Inline fillTablesST #-}
fillTablesST ts = runST $ fillTables ts

-- |

fillTables
--  ∷ Proxy (BigOrderNats ts)
--  -- ^ Proxy that provides the set of @BigOrder@ naturals
  ∷ forall bigOrder s ts
  . ( bigOrder ~ BigOrderNats ts
    , EachBigOrder bigOrder ts)
  ⇒ ts
  -- ^ The tables
  → ST s ts
{-# Inline fillTables #-}
fillTables ts = do
  --fillEachBigOrder (Proxy ∷ Proxy (BigOrderNats ts)) ts
  eachBigOrder (Proxy ∷ Proxy bigOrder) ts
  return ts

-- | This type class instanciates to the specialized machinery for each
-- @BigOrder Natural@ number.

class EachBigOrder (boNats ∷ [Nat]) ts where
  eachBigOrder ∷ Proxy boNats → ts → ST s ()

-- | No more big orders to handle.

instance EachBigOrder '[] ts where
  {-# Inline eachBigOrder #-}
  eachBigOrder Proxy _ = return ()

-- | handle this big order.

instance
  ( EachBigOrder ns ts
  , ThisBigOrder n (IsThisBigOrder n ts) ts
  ) ⇒ EachBigOrder (n ': ns) ts where
  {-# Inline eachBigOrder #-}
  eachBigOrder Proxy ts = do
    thisBigOrder (Proxy ∷ Proxy n) (Proxy ∷ Proxy (IsThisBigOrder n ts)) ts
    eachBigOrder (Proxy ∷ Proxy ns) ts

-- |

class ThisBigOrder (boNat ∷ Nat) (thisOrder ∷ Bool) ts where
  thisBigOrder ∷ Proxy boNat → Proxy thisOrder → ts → ST s ()
  getAllBounds ∷ Proxy boNat → Proxy thisOrder → ts → [()]

instance ThisBigOrder boNat anyOrder Z where
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy Z = return ()
  {-# Inline getAllBounds #-}
  getAllBounds Proxy Proxy Z = []

-- | We have found the first table for our big order. Extract the bounds and
-- hand over to small order. We do not need to check for another big order with
-- this nat, since all tables are now being filled by the small order.

instance
  ( smallOrder ~ SmallOrderNats (ts:.TwITbl bo m arr c i x)
  , EachSmallOrder boNat smallOrder (ts:.TwITbl bo m arr c i x) i
  , PrimArrayOps arr i x
  , IndexStream i
  ) ⇒ ThisBigOrder boNat True (ts:.TwITbl bo m arr c i x) where
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy tst@(_:.TW (ITbl lo _ arr) _) = do
    let to = upperBound arr
    let allBounds = getAllBounds (Proxy ∷ Proxy boNat) (Proxy ∷ Proxy True) tst
    -- TODO check bounds
    flip SM.mapM_ (streamUp zeroBound' to) $ \k ->
      eachSmallOrder (Proxy ∷ Proxy boNat) (Proxy ∷ Proxy smallOrder) tst k
  {-# Inline getAllBounds #-}
  getAllBounds Proxy Proxy (ts:.t) = undefined

-- | Go down the tables until we find the first table for our big order.

instance
  ( ThisBigOrder n (IsThisBigOrder n ts) ts
  ) ⇒ ThisBigOrder n False (ts:.t) where
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy (ts:.t) =
    thisBigOrder (Proxy ∷ Proxy n) (Proxy ∷ Proxy (IsThisBigOrder n ts)) ts

-- |

class EachSmallOrder (bigOrder ∷ Nat) (smallOrders ∷ [Nat]) ts i where
  eachSmallOrder
    ∷ Proxy bigOrder
    -- ^ Only fill exactly this big order
    → Proxy smallOrders
    -- ^ These are all the small order to go through.
    → ts
    -- ^ set of tables.
    → i
    -- ^ index to update.
    → ST s ()

-- | Went through all tables, nothing more to do.

instance EachSmallOrder bigOrder '[] ts i where
  {-# Inline eachSmallOrder #-}
  eachSmallOrder Proxy Proxy ts i = return ()

-- | 

instance
  ( EachSmallOrder bigOrder so ts i
  , isThisBigOrder ~ IsThisBigOrder bigOrder ts
  , isThisSmallOrder ~ IsThisSmallOrder s ts
  , isThisOrder ~ (:&&) isThisBigOrder isThisSmallOrder
  , ThisSmallOrder bigOrder s isThisOrder ts i
  ) ⇒ EachSmallOrder bigOrder (s ': so) ts i where
  {-# Inline eachSmallOrder #-}
  eachSmallOrder Proxy Proxy ts i = do
    -- fill all tables that have the same big & small order
    thisSmallOrder (Proxy ∷ Proxy bigOrder) (Proxy ∷ Proxy s) (Proxy ∷ Proxy isThisOrder) ts i
    -- fill tables with the next small order
    eachSmallOrder (Proxy ∷ Proxy bigOrder) (Proxy ∷ Proxy so) ts i

-- |

class ThisSmallOrder (bigNat ∷ Nat) (smallNat ∷ Nat) (thisOrder ∷ Bool) ts i where
  thisSmallOrder ∷ Proxy bigNat → Proxy smallNat → Proxy thisOrder → ts → i → ST s ()

instance ThisSmallOrder b s any Z i where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder _ _ _ _ _ = return ()

instance
  ( isThisBigOrder ~ IsThisBigOrder bigOrder ts
  , isThisSmallOrder ~ IsThisSmallOrder smallOrder ts
  , isThisOrder ~ (:&&) isThisBigOrder isThisSmallOrder
  , ThisSmallOrder bigOrder smallOrder isThisOrder ts i
  ) ⇒ ThisSmallOrder bigOrder smallOrder 'False (ts:.t) i where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder Proxy Proxy Proxy (ts:.t) i =
    thisSmallOrder (Proxy ∷ Proxy bigOrder) (Proxy ∷ Proxy smallOrder) (Proxy ∷ Proxy isThisOrder) ts i

-- |
--
-- TODO generalize from @Id@ to any monad in a stack with a primitive base

instance
  ( PrimArrayOps arr i x
  , MPrimArrayOps arr i x
  ) ⇒ ThisSmallOrder bigOrder smallOrder 'True (ts:.TwITbl bo Id arr c i x) i where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder Proxy Proxy Proxy (ts:.TW (ITbl lo _ arr) f) i = do
    let uB = undefined
    marr <- unsafeThaw arr
    z ← return . unId $ f uB i
    writeM marr i z

-- | The set of arrays to fill is a tuple of the form @(Z:.a:.b:.c)@. Here, we
-- extract the big order @Nat@s. The set of @Nat@s being returned is already
-- ordered with the smallest @Nat@ up front.

type BigOrderNats arr = Nub (Sort (BigOrderNats' arr))

type family BigOrderNats' arr ∷ [Nat]

type instance BigOrderNats' Z = '[]

type instance BigOrderNats' (ts:.TwITbl bo m arr c i x) = bo ': BigOrderNats' ts



type family IsThisBigOrder (n ∷ Nat) arr ∷ Bool

type instance IsThisBigOrder n Z = 'False

type instance IsThisBigOrder n (ts:.TwITbl bo m arr c i x) = n == bo



type SmallOrderNats arr = Nub (Sort (SmallOrderNats' arr))

type family SmallOrderNats' arr ∷ [Nat]

type instance SmallOrderNats' Z = '[]

-- TODO fix small order

type instance SmallOrderNats' (ts:.TwITbl bo m arr c i x) = 1 ': SmallOrderNats' ts



type family IsThisSmallOrder (n ∷ Nat) arr ∷ Bool

type instance IsThisSmallOrder n Z = 'False

-- TODO fix small order comparision

type instance IsThisSmallOrder n (ts:.TwITbl bo m arr c i x) = n == 1

