
-- |
--
-- TODO Need to add additional type family instances as required.
--
-- TODO Need to have little order nats as well.

module ADP.Fusion.Core.SynVar.FillTyLvl where

import           Control.DeepSeq
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Proxy
import           Data.Singletons.Prelude.Bool
import           Data.Singletons.Prelude.Bool
import           Data.Singletons.Prelude.List
import           Data.Type.Equality
import           Data.Vector.Fusion.Util (Id(..))
import           Debug.Trace (traceShow)
import           GHC.Exts
import           GHC.Generics
import           GHC.TypeNats
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector as V
import           System.CPUTime
import           Text.Printf

import           Data.PrimitiveArray
import qualified Data.PrimitiveArray.Sparse as PAS

import           ADP.Fusion.Core.SynVar.TableWrap
import           ADP.Fusion.Core.SynVar.Array



-- |

fillTables
  :: forall bigOrder s ts
  .  ( bigOrder ~ BigOrderNats ts
     , EachBigOrder bigOrder ts
     , CountNumberOfCells 0 ts
  )
  => ts
  -- ^ The tables
  -> ST s (Mutated ts)
{-# Inline fillTables #-}
fillTables ts = do
  !startTime <- unsafeIOToPrim getCPUTime
  ps <- eachBigOrder (Proxy :: Proxy bigOrder) ts
  !stopTime  <- unsafeIOToPrim getCPUTime
  let deltaTime = max 1 $ stopTime - startTime
  return $! Mutated
    { mutatedTables = ts
    , perfCounter   = PerfCounter
        { picoSeconds   = deltaTime
        , seconds       = 1e-12 * fromIntegral deltaTime
        , numberOfCells = countNumberOfCells (Nothing ∷ Maybe (Proxy 0)) ts
        }
    , eachBigPerfCounter = ps
    }

-- | This type class instanciates to the specialized machinery for each
-- @BigOrder Natural@ number.

class EachBigOrder (boNats :: [Nat]) ts where
  eachBigOrder :: Proxy boNats -> ts -> ST s [PerfCounter]

-- | No more big orders to handle.

instance EachBigOrder '[] ts where
  {-# Inline eachBigOrder #-}
  eachBigOrder Proxy _ = return []

-- | handle this big order.

instance
  ( EachBigOrder ns ts
  , ThisBigOrder n (IsThisBigOrder n ts) ts
  , CountNumberOfCells n ts
  ) => EachBigOrder (n ': ns) ts where
  {-# Inline eachBigOrder #-}
  eachBigOrder Proxy ts = do
    !startTime <- unsafeIOToPrim getCPUTime
    thisBigOrder (Proxy :: Proxy n) (Proxy :: Proxy (IsThisBigOrder n ts)) ts
    !stopTime  <- unsafeIOToPrim getCPUTime
    let deltaTime = max 1 $ stopTime - startTime
    ps <- eachBigOrder (Proxy :: Proxy ns) ts
    let p = PerfCounter
              { picoSeconds   = deltaTime
              , seconds       = 1e-12 * fromIntegral deltaTime
              , numberOfCells = countNumberOfCells (Just (Proxy ∷ Proxy n)) ts
              }
    return $ p:ps

-- | 'ThisBigOrder' provides machinery to fill tables correctly.
--
-- TODO @getAllBounds@ should return a sum structure providing either dense bounds, banded bounds,
-- or a sparse set of elements, for @streamUp/streamDown@ to work on. This is currently not
-- happening.

class ThisBigOrder (boNat ∷ Nat) (thisOrder ∷ Bool) ts where
  thisBigOrder ∷ Proxy boNat → Proxy thisOrder → ts → ST s ()
  getAllBounds ∷ Proxy boNat → Proxy thisOrder → ts → [()]

instance ThisBigOrder boNat anyOrder Z where
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy Z = return ()
  {-# Inline getAllBounds #-}
  getAllBounds Proxy Proxy Z = []

-- | For 'Dense' tables, we have found the first table for our big order. Extract the bounds and
-- hand over to small order. We do not need to check for another big order with this nat, since all
-- tables are now being filled by the small order.

instance
  ( smallOrder ~ SmallOrderNats (ts:.TwITbl bo so m (Dense v) c i x)
  , EachSmallOrder boNat smallOrder (ts:.TwITbl bo so m (Dense v) c i x) i
  , PrimArrayOps (Dense v) i x
  , IndexStream i
  ) ⇒ ThisBigOrder boNat True (ts:.TwITbl bo so m (Dense v) c i x) where
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy tst@(_:.TW (ITbl _ arr) _) = do
    let to = upperBound arr
    let allBounds = getAllBounds (Proxy ∷ Proxy boNat) (Proxy ∷ Proxy True) tst
    -- TODO This should provide one of a multitude of different ways to stream indices: for dense
    -- matrices, use what is below, but for other types, we will need unions of indices.
    flip SM.mapM_ (streamUp zeroBound' to) $ \k ->
      eachSmallOrder (Proxy ∷ Proxy boNat) (Proxy ∷ Proxy smallOrder) tst k
  {-# Inline getAllBounds #-}
  getAllBounds Proxy Proxy (ts:.t) = undefined

-- | For 'Sparse' tables, we have found the first table ...

instance
  ( smallOrder ~ SmallOrderNats (ts:.TwITbl bo so m (PAS.Sparse ixw v) c i x)
  , EachSmallOrder boNat smallOrder (ts:.TwITbl bo so m (PAS.Sparse ixw v) c i x) i
  , PrimArrayOps (PAS.Sparse ixw v) i x
  , IndexStream i
  , VG.Vector ixw i
  ) ⇒ ThisBigOrder boNat True (ts:.TwITbl bo so m (PAS.Sparse ixw v) c i x) where
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy tst@(_:.TW (ITbl _ arr) _) = do
    -- TODO merge all indices, this system only works partially for now!
    let ixs = V.map (fromLinearIndex $ PAS.sparseUpperBound arr) $ V.convert $ PAS.sparseIndices arr
    traceShow "WARNING: mergeIndices has not happened yet! All sparse tables need to have the union of indices!" $
      flip V.mapM_ ixs $ \k ->
        eachSmallOrder (Proxy ∷ Proxy boNat) (Proxy ∷ Proxy smallOrder) tst k

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
  , isThisOrder ~ (isThisBigOrder && isThisSmallOrder)
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
  , isThisOrder ~ (isThisBigOrder && isThisSmallOrder)
  , ThisSmallOrder bigOrder smallOrder isThisOrder ts i
  ) ⇒ ThisSmallOrder bigOrder smallOrder 'False (ts:.t) i where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder Proxy Proxy Proxy (ts:.t) i =
    thisSmallOrder (Proxy ∷ Proxy bigOrder) (Proxy ∷ Proxy smallOrder) (Proxy ∷ Proxy isThisOrder) ts i

-- | This instance fills only dense tables. Sparse tables will use a slightly different system,
-- where writes may fail silently!
--
-- TODO generalize from @Id@ to any monad in a stack with a primitive base

instance
  ( PrimArrayOps (Dense v) i x
  , isThisBigOrder ~ IsThisBigOrder bigOrder ts
  , isThisSmallOrder ~ IsThisSmallOrder smallOrder ts
  , isThisOrder ~ (isThisBigOrder && isThisSmallOrder)
  , ThisSmallOrder bigOrder smallOrder isThisOrder ts i
  ) ⇒ ThisSmallOrder bigOrder smallOrder 'True (ts:.TwITbl bo so Id (Dense v) c i x) i where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder Proxy Proxy Proxy (ts:.TW (ITbl _ arr) f) i = do
    let uB = upperBound arr
    marr <- unsafeThawM arr
    z <- return . unId $ f uB i
    writeM marr i z
    -- TODO need to write test case that checks that all tables are always filled
    thisSmallOrder (Proxy ∷ Proxy bigOrder) (Proxy ∷ Proxy smallOrder) (Proxy ∷ Proxy isThisOrder) ts i

instance
  ( PrimArrayOps (PAS.Sparse ixw v) i x
  , Index i
  , SparseBucket i, Ord i
  , VG.Vector ixw i
  , VG.Vector v x
  , Show i, Show x
  , isThisBigOrder ~ IsThisBigOrder bigOrder ts
  , isThisSmallOrder ~ IsThisSmallOrder smallOrder ts
  , isThisOrder ~ (isThisBigOrder && isThisSmallOrder)
  , ThisSmallOrder bigOrder smallOrder isThisOrder ts i
  ) ⇒ ThisSmallOrder bigOrder smallOrder 'True (ts:.TwITbl bo so Id (PAS.Sparse ixw v) c i x) i where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder Proxy Proxy Proxy (ts:.TW (ITbl _ arr) f) i = do
    let uB = upperBound arr
    marr <- unsafeThawM arr
    z ← return . unId $ f uB i
    safeWriteM marr i z
    -- TODO need to write test case that checks that all tables are always filled
    thisSmallOrder (Proxy ∷ Proxy bigOrder) (Proxy ∷ Proxy smallOrder) (Proxy ∷ Proxy isThisOrder) ts i

-- | The set of arrays to fill is a tuple of the form @(Z:.a:.b:.c)@. Here, we
-- extract the big order @Nat@s. The set of @Nat@s being returned is already
-- ordered with the smallest @Nat@ up front.

type BigOrderNats arr = Nub (Sort (BigOrderNats' arr))

type family BigOrderNats' arr ∷ [Nat]

type instance BigOrderNats' Z = '[]

type instance BigOrderNats' (ts:.TwITbl bo so m arr c i x) = bo ': BigOrderNats' ts



type family IsThisBigOrder (n ∷ Nat) arr ∷ Bool

type instance IsThisBigOrder n Z = 'False

type instance IsThisBigOrder n (ts:.TwITbl bo so m arr c i x) = n == bo



type SmallOrderNats arr = Nub (Sort (SmallOrderNats' arr))

type family SmallOrderNats' arr ∷ [Nat]

type instance SmallOrderNats' Z = '[]

-- TODO fix small order

type instance SmallOrderNats' (ts:.TwITbl bo so m arr c i x) = so ': SmallOrderNats' ts



type family IsThisSmallOrder (n ∷ Nat) arr ∷ Bool

type instance IsThisSmallOrder n Z = 'False

-- TODO fix small order comparision

type instance IsThisSmallOrder n (ts:.TwITbl bo so m arr c i x) = n == so

data Mutated ts = Mutated
  { mutatedTables ∷ !ts
  , perfCounter   ∷ !PerfCounter
  , eachBigPerfCounter  ∷ [PerfCounter]
  }
  deriving (Eq,Ord,Show,Generic)

instance NFData ts ⇒ NFData (Mutated ts)

data PerfCounter = PerfCounter
  { picoSeconds   :: !Integer
  , seconds       :: !Double
  , numberOfCells :: !Integer
  }
  deriving (Eq,Ord,Show,Generic)

instance NFData PerfCounter

showPerfCounter ∷ PerfCounter → String
{-# NoInline showPerfCounter #-}
showPerfCounter PerfCounter{..} =
  let cellsSecond = round $ fromIntegral numberOfCells / seconds
      m ∷ Integer = 1000000
  in  printf "%.4f seconds, %d,%06d cells @ %d,%06d cells/second"
             seconds
             (numberOfCells `div` m) (numberOfCells `mod` m)
             (cellsSecond `div` m) (cellsSecond `mod` m)

-- | Adding two 'PerfCounter's yields the time they take together.

instance Num PerfCounter where
  PerfCounter p1 s1 n1 + PerfCounter p2 s2 n2 = PerfCounter (p1+p2) (s1+s2) (n1+n2)


class CountNumberOfCells (n ∷ Nat) t where
  countNumberOfCells ∷ Maybe (Proxy n) → t → Integer

instance CountNumberOfCells n Z where
  {-# NoInline countNumberOfCells #-}
  countNumberOfCells p Z = 0

instance
  ( CountNumberOfCells n ts
  , Index i
  , PrimArrayOps arr i x
  , KnownNat n
  , KnownNat bo
  ) ⇒ CountNumberOfCells n (ts:.TwITbl bo so Id arr c i x) where
  {-# NoInline countNumberOfCells #-}
  countNumberOfCells mayP (ts:.(TW (ITbl _ arr) fun)) =
    let n  = natVal (Proxy ∷ Proxy n)
        bo = natVal (Proxy ∷ Proxy bo)
        cs = countNumberOfCells mayP ts
        c  = product . totalSize $ upperBound arr
    in  case mayP of
      Nothing → cs + c
      Just _  → cs + if n==bo then c else 0

