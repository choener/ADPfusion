
-- |
--
-- TODO Need to add additional type family instances as required.
--
-- TODO Need to have little order nats as well.

module ADP.Fusion.Core.SynVar.FillTyLvl where

import           GHC.TypeNats
import           Data.Promotion.Prelude.List

import           Data.PrimitiveArray

import           ADP.Fusion.Core.SynVar.Array



-- | The set of arrays to fill is a tuple of the form @(Z:.a:.b:.c)@. Here, we
-- extract the big order @Nat@s. The set of @Nat@s being returned is already
-- ordered with the smallest @Nat@ up front.

type BigOrderNats arr = Nub (Sort (BigOrderNats' arr))

type family BigOrderNats' arr ∷ [Nat]

type instance BigOrderNats' Z = '[]

type instance BigOrderNats' (ts:.TwITbl bo m arr c i x) = bo ': BigOrderNats ts

