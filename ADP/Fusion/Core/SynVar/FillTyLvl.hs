
-- |
--
-- TODO Need to add additional type family instances as required.
--
-- TODO Need to have little order nats as well.

module ADP.Fusion.Core.SynVar.FillTyLvl where

import           GHC.TypeNats
import           GHC.Exts
import           Data.Promotion.Prelude.List
import           Data.Promotion.Prelude.Bool
import           Data.Singletons.Prelude.Bool
import           Control.Monad.ST
import           Data.Proxy
import           Data.Type.Equality
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU

import           Data.PrimitiveArray

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

instance EachBigOrder '[] ts where
  {-# Inline eachBigOrder #-}
  eachBigOrder Proxy _ = return ()

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
  , EachSmallOrder boNat smallOrder (ts:.TwITbl bo m arr c i x)
  ) ⇒ ThisBigOrder boNat True (ts:.TwITbl bo m arr c i x) where
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy tst@(_:.t) = do
    let allBounds = getAllBounds (Proxy ∷ Proxy boNat) (Proxy ∷ Proxy True) tst
    -- TODO check bounds
    -- TODO run loop
    -- TODO fill cells with small orders using @eachSmallOrder@.
    do eachSmallOrder (Proxy ∷ Proxy boNat) (Proxy ∷ Proxy smallOrder) tst ()
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

class EachSmallOrder (bigOrder ∷ Nat) (smallOrders ∷ [Nat]) ts where
  eachSmallOrder
    ∷ Proxy bigOrder
    -- ^ Only fill exactly this big order
    → Proxy smallOrders
    -- ^ These are all the small order to go through.
    → ts
    -- ^ set of tables.
    → ()
    -- ^ index to update.
    → ST s ()

instance EachSmallOrder bigOrder '[] ts where
  {-# Inline eachSmallOrder #-}
  eachSmallOrder Proxy Proxy ts () = return ()

instance
  ( EachSmallOrder bigOrder so ts
  , isThisBigOrder ~ IsThisBigOrder bigOrder ts
  , isThisSmallOrder ~ IsThisSmallOrder s ts
  , isThisOrder ~ (:&&) isThisBigOrder isThisSmallOrder
  , ThisSmallOrder bigOrder s isThisOrder ts
  ) ⇒ EachSmallOrder bigOrder (s ': so) ts where
  {-# Inline eachSmallOrder #-}
  eachSmallOrder Proxy Proxy ts i = do
    thisSmallOrder (Proxy ∷ Proxy bigOrder) (Proxy ∷ Proxy s) (Proxy ∷ Proxy isThisOrder) ts i
    eachSmallOrder (Proxy ∷ Proxy bigOrder) (Proxy ∷ Proxy so) ts ()

-- |

class ThisSmallOrder (bigNat ∷ Nat) (smallNat ∷ Nat) (thisOrder ∷ Bool) ts where
  thisSmallOrder ∷ Proxy bigNat → Proxy smallNat → Proxy thisOrder → ts → () → ST s ()

instance ThisSmallOrder b s any Z where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder _ _ _ _ _ = return ()

instance ThisSmallOrder bigOrder smallOrder 'False (t:.ts) where

instance ThisSmallOrder bigOrder smallOrder 'True (t:.ts) where

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

