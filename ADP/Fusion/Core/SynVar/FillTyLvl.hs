
-- |
--
-- TODO Need to add additional type family instances as required.
--
-- TODO Need to have little order nats as well.

module ADP.Fusion.Core.SynVar.FillTyLvl where

import           GHC.TypeNats
import           GHC.Exts
import           Data.Promotion.Prelude.List
import           Control.Monad.ST
import           Data.Proxy
import           Data.Type.Equality

import           Data.PrimitiveArray

import           ADP.Fusion.Core.SynVar.Array



-- | Fill/mutate tables using @ST@.

fillTablesST
  ∷ forall bigOrder ts
  . ( bigOrder ~ BigOrderNats ts
    , FillEachBigOrder bigOrder ts
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
    , FillEachBigOrder bigOrder ts)
  ⇒ ts
  -- ^ The tables
  → ST s ts
{-# Inline fillTables #-}
fillTables ts = do
  --fillEachBigOrder (Proxy ∷ Proxy (BigOrderNats ts)) ts
  fillEachBigOrder (Proxy ∷ Proxy bigOrder) ts
  return ts

-- | This type class instanciates to the specialized machinery for each
-- @BigOrder Natural@ number.

class FillEachBigOrder (boNats ∷ [Nat]) ts where
  fillEachBigOrder ∷ Proxy boNats → ts → ST s ()

instance FillEachBigOrder '[] ts where
  {-# Inline fillEachBigOrder #-}
  fillEachBigOrder Proxy _ = return ()

instance
  ( FillEachBigOrder ns ts
  , FillThisBigOrder n (IsThisBigOrderTable n ts) ts
  ) ⇒ FillEachBigOrder (n ': ns) ts where
  {-# Inline fillEachBigOrder #-}
  fillEachBigOrder Proxy ts = do
    fillThisBigOrder (Proxy ∷ Proxy n) (Proxy ∷ Proxy (IsThisBigOrderTable n ts)) ts
    fillEachBigOrder (Proxy ∷ Proxy ns) ts

-- |

class FillThisBigOrder (boNat ∷ Nat) (thisOrder ∷ Bool) ts where
  fillThisBigOrder ∷ Proxy boNat → Proxy thisOrder → ts → ST s ()
  getAllBounds ∷ Proxy boNat → Proxy thisOrder → ts → [()]

instance FillThisBigOrder boNat anyOrder Z where
  {-# Inline fillThisBigOrder #-}
  fillThisBigOrder Proxy Proxy Z = return ()
  {-# Inline getAllBounds #-}
  getAllBounds Proxy Proxy Z = []

-- | We have found the first table for our big order. Extract the bounds and
-- hand over to small order. We do not need to check for another big order with
-- this nat, since all tables are now being filled by the small order.

instance FillThisBigOrder boNat True (ts:.TwITbl bo m arr c i x) where
  {-# Inline fillThisBigOrder #-}
  fillThisBigOrder Proxy Proxy tst@(_:.t) = do
    let allBounds = getAllBounds (Proxy ∷ Proxy boNat) (Proxy ∷ Proxy True) tst
    -- TODO run loop
    -- TODO fill cells with small orders.
    return ()
  {-# Inline getAllBounds #-}
  getAllBounds Proxy Proxy (ts:.t) = undefined

-- | Go down the tables until we find the first table for our big order.

instance
  ( FillThisBigOrder n (IsThisBigOrderTable n ts) ts
  ) ⇒ FillThisBigOrder n False (ts:.t) where
  {-# Inline fillThisBigOrder #-}
  fillThisBigOrder Proxy Proxy (ts:.t) = do
    fillThisBigOrder (Proxy ∷ Proxy n) (Proxy ∷ Proxy (IsThisBigOrderTable n ts)) ts

-- |

class FillThisSmallOrder (bigNat ∷ Nat) (smallNat ∷ Nat) (thisOrder ∷ Bool) ts where
  fillThisSmallOrder ∷ Proxy bigNat → Proxy smallNat → Proxy thisOrder → ts → ST s ()

instance FillThisSmallOrder b s any Z where
  {-# Inline fillThisSmallOrder #-}
  fillThisSmallOrder _ _ _ _ = return ()

-- | The set of arrays to fill is a tuple of the form @(Z:.a:.b:.c)@. Here, we
-- extract the big order @Nat@s. The set of @Nat@s being returned is already
-- ordered with the smallest @Nat@ up front.

type BigOrderNats arr = Nub (Sort (BigOrderNats' arr))

type family BigOrderNats' arr ∷ [Nat]

type instance BigOrderNats' Z = '[]

type instance BigOrderNats' (ts:.TwITbl bo m arr c i x) = bo ': BigOrderNats ts



type family IsThisBigOrderTable (n ∷ Nat) arr ∷ Bool

type instance IsThisBigOrderTable n Z = 'False

type instance IsThisBigOrderTable n (ts:.TwITbl bo m arr c i x) = n == bo

