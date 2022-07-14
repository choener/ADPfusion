
-- |
--
-- TODO Need to add additional type family instances as required.
--
-- TODO Need to have little order nats as well.

module ADPfusion.Core.SynVar.FillTyLvl where

import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Bool.Singletons
import           Data.List.Singletons
import           Data.Proxy
import           Data.Type.Equality
import           Data.Vector.Fusion.Util (Id(..))
import           Debug.Trace (traceShow)
import           GHC.Exts
import           GHC.Generics
import           GHC.TypeNats
import           GHC.TypeLits (TypeError(..), ErrorMessage(..))
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import           System.CPUTime
import           Text.Printf

import           Data.PrimitiveArray
import qualified Data.PrimitiveArray.Sparse as PAS

import           ADPfusion.Core.SynVar.TableWrap
import           ADPfusion.Core.SynVar.Array


-- * Very simple type-level based lookup table

-- | Associate a bigorder index (BOI) with a particular shape @sh@. This shape, typically an upper
-- bound, will be used further down to initialize a loop over indices.

data BOI (bigOrder :: Nat) sh = BOI sh

-- | "Start" function to find a big order index. @cmp@ does a type-level equality check between the
-- proxy we test against, and the lookup table.
-- @findboi (Proxy @1) (Z:.BOI @0 ():.BOI @1 'A')@ will return @'A'@.

findboi
  :: forall cmp ls (that::Nat) tsh (fnd::Nat)
  . (cmp ~ (that == fnd), FindBOI cmp (ls:.BOI that tsh) fnd)
  => (ls:.BOI that tsh) -> Proxy fnd -> RetTy cmp (ls:.BOI that tsh) fnd
--{{{
{-# Inline findboi #-}
findboi = findboi' (Proxy :: Proxy cmp)
--}}}

class FindBOI (tf :: Bool) down (bigOrder :: Nat) where
--{{{
  -- | We need to compute the actual return type, based on the incoming type.
  type RetTy tf down bigOrder :: *
  -- | Recursively scan the lookup table.
  findboi' :: Proxy tf -> down -> Proxy bigOrder -> RetTy tf down bigOrder
--}}}

instance FindBOI tf Z fnd where
--{{{
  type RetTy tf Z fnd = TypeError (Text "Missing FindBOI instance in lookup table for bigorder Nat: " :<>: ShowType fnd)
  {-# Inline findboi' #-}
  findboi' = undefined -- impossible to write this instance now!
--}}}

instance (sh ~ ret) => FindBOI True (ls:.BOI this sh) fnd where
--{{{
  type RetTy True (ls:.BOI this sh) fnd = sh
  {-# Inline findboi' #-}
  findboi' _ (_ :. BOI sh) _ = sh
--}}}

instance (cmp ~ (that == fnd), FindBOI cmp (ls:.BOI that tsh) fnd) => FindBOI False ((ls:.BOI that tsh):.BOI this sh) fnd where
--{{{
  type RetTy False (ls:.BOI that tsh:.BOI this sh) fnd = RetTy (that==fnd) (ls:.BOI that tsh) fnd
  {-# Inline findboi' #-}
  findboi' _ (ls:._) = findboi' (Proxy :: Proxy cmp) ls
--}}}


-- | This version of @fillTables@ requires an explicit 'LimitType', which allows us to handle
-- heterogenous tables.
--
-- The 'BigOrderNats' type-level function extracts the number of stages.
--
-- TODO This is still kind-of a hack, since we need to be more explicit yet on how to fill tables
-- that are shape-smaller than the given shape ...
--
-- TODO we should actually have a LimitType thing for each individual big order table, since those
-- should be possible to be different.

fillTablesDim
  :: forall bigOrder s ts sh boi
  .  (bigOrder ~ BigOrderNats ts, EachBigOrder bigOrder ts boi, CountNumberOfCells 0 ts)
  => boi -> ts -> ST s (Mutated ts)
--{{{
{-# Inline fillTablesDim #-}
fillTablesDim sh ts = do
  !startTime <- unsafeIOToPrim getCPUTime
  ps <- eachBigOrder (Proxy :: Proxy bigOrder) ts sh
  !stopTime  <- unsafeIOToPrim getCPUTime
  let deltaTime = max 1 $ stopTime - startTime
  return $! Mutated
    { mutatedTables = ts
    , perfCounter   = PerfCounter
        { picoSeconds   = deltaTime
        , seconds       = 1e-12 * fromIntegral deltaTime
        , numberOfCells = countNumberOfCells (Nothing :: Maybe (Proxy 0)) ts
        }
    , eachBigPerfCounter = ps
    }
--}}}

-- |
--
-- TODO we should have a variant that receives an explicit object with boundary dimensions. This
-- will help with heterogenous table designs for pseudoknots. Then 'fillTables' will just extract
-- the shape of the first table and use 'fillTablesDim'. Thereby we have a unified system for
-- handling this.

fillTables
  :: forall bigOrder s ts
  .  (bigOrder ~ BigOrderNats ts, EachBigOrder bigOrder ts (), CountNumberOfCells 0 ts)
  => ts -> ST s (Mutated ts)
--{{{
{-# Inline  fillTables #-}
fillTables ts = do
  !startTime <- unsafeIOToPrim getCPUTime
  ps <- eachBigOrder (Proxy :: Proxy bigOrder) ts ()
  !stopTime  <- unsafeIOToPrim getCPUTime
  let deltaTime = max 1 $ stopTime - startTime
  return $! Mutated
    { mutatedTables = ts
    , perfCounter   = PerfCounter
        { picoSeconds   = deltaTime
        , seconds       = 1e-12 * fromIntegral deltaTime
        , numberOfCells = countNumberOfCells (Nothing :: Maybe (Proxy 0)) ts
        }
    , eachBigPerfCounter = ps
    }
--}}}

-- | This type class instanciates to the specialized machinery for each
-- @BigOrder Natural@ number. @BigOrder@'s separate "logical stages" of a dynamic programming
-- algorithm, that are not interdependent, but are rather run one after another. Of course later
-- stages may use data from earlier stages, but not vice versa.

class EachBigOrder (boNats :: [Nat]) ts gi where
--{{{
  eachBigOrder :: Proxy boNats -> ts -> gi -> ST s [PerfCounter]
--}}}

-- | No more big orders to handle.

instance EachBigOrder '[] ts gi where
  {-# Inline eachBigOrder #-}
  eachBigOrder Proxy _ _ = return []

-- | handle this big order.

instance
  ( EachBigOrder ns ts gi, ThisBigOrder n (IsThisBigOrder n ts) ts gi, CountNumberOfCells n ts)
  => EachBigOrder (n ': ns) ts gi where
--{{{
  {-# Inline eachBigOrder #-}
  eachBigOrder Proxy ts gi = do
    !startTime <- unsafeIOToPrim getCPUTime
    thisBigOrder (Proxy :: Proxy n) (Proxy :: Proxy (IsThisBigOrder n ts)) ts gi
    !stopTime  <- unsafeIOToPrim getCPUTime
    let deltaTime = max 1 $ stopTime - startTime
    ps <- eachBigOrder (Proxy :: Proxy ns) ts gi
    let p = PerfCounter
              { picoSeconds   = deltaTime
              , seconds       = 1e-12 * fromIntegral deltaTime
              , numberOfCells = countNumberOfCells (Just (Proxy :: Proxy n)) ts
              }
    return $ p:ps
--}}}

-- | 'ThisBigOrder' provides machinery to fill tables correctly.
--
-- TODO @getAllBounds@ should return a sum structure providing either dense bounds, banded bounds,
-- or a sparse set of elements, for @streamUp/streamDown@ to work on. This is currently not
-- happening.

class ThisBigOrder (boNat :: Nat) (thisOrder :: Bool) ts gi where
  thisBigOrder :: Proxy boNat -> Proxy thisOrder -> ts -> gi -> ST s ()

instance ThisBigOrder boNat anyOrder Z gi where
--{{{
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy Z _ = return ()
--}}}

-- | For 'Dense' tables, we have found the first table for our big order. Extract the bounds and
-- hand over to small order. We do not need to check for another big order with this nat, since all
-- tables are now being filled by the small order.

instance
  ( smallOrder ~ SmallOrderNats (ts:.TwITbl bo so m (Dense v) c i x)
  , EachSmallOrder boNat smallOrder (ts:.TwITbl bo so m (Dense v) c i x) i
  , PrimArrayOps (Dense v) i x
  , IndexStream i
  ) => ThisBigOrder boNat True (ts:.TwITbl bo so m (Dense v) c i x) () where
  {-# Inline thisBigOrder #-}
--{{{
  thisBigOrder Proxy Proxy tst@(_:.TW (ITbl _ arr) _) gi = do
    let to = upperBound arr
    SM.mapM_ (eachSmallOrder (Proxy @boNat) (Proxy @smallOrder) tst) (streamUp zeroBound' to)
--}}}

instance
  ( smallOrder ~ SmallOrderNats (ts:.TwITbl bo so m (Dense v) c i x)
  , EachSmallOrder boNat smallOrder (ts:.TwITbl bo so m (Dense v) c i x) streamTy
  , FindBOI (that == boNat) (ls:.BOI that tsh) boNat
  , LimitType streamTy ~ RetTy (that==boNat) (ls:.BOI that tsh) boNat
  , Index streamTy, IndexStream streamTy
  ) => ThisBigOrder boNat True (ts:.TwITbl bo so m (Dense v) c i x) (ls:.BOI that tsh) where
--{{{
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy tst@(_:.TW (ITbl _ _) _) gi = do
    let boi = findboi gi (Proxy :: Proxy boNat)
    flip SM.mapM_ (streamUp zeroBound' boi) $ \k ->
      eachSmallOrder (Proxy :: Proxy boNat) (Proxy :: Proxy smallOrder) tst k
--}}}

-- | For 'Sparse' tables, we have found the first table ...

instance
  ( smallOrder ~ SmallOrderNats (ts:.TwITbl bo so m (PAS.Sparse ixw v) c i x)
  , EachSmallOrder boNat smallOrder (ts:.TwITbl bo so m (PAS.Sparse ixw v) c i x) i
  , PrimArrayOps (PAS.Sparse ixw v) i x
  , IndexStream i
  , VG.Vector ixw i
  ) => ThisBigOrder boNat True (ts:.TwITbl bo so m (PAS.Sparse ixw v) c i x) gi where
--{{{
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy tst@(_:.TW (ITbl _ arr) _) gi = do
    -- TODO merge all indices, this system only works partially for now!
    let ixs = V.map (fromLinearIndex $ PAS.sparseUpperBound arr) $ V.convert $ PAS.sparseIndices arr
    traceShow "WARNING: mergeIndices has not happened yet! All sparse tables need to have the union of indices!" $
      flip V.mapM_ ixs $ \k ->
        eachSmallOrder (Proxy :: Proxy boNat) (Proxy :: Proxy smallOrder) tst k
--}}}

-- | Go down the tables until we find the first table for our big order.

instance
  ( ThisBigOrder n (IsThisBigOrder n ts) ts gi
  ) => ThisBigOrder n False (ts:.t) gi where
  {-# Inline thisBigOrder #-}
  thisBigOrder Proxy Proxy (ts:.t) =
    thisBigOrder (Proxy :: Proxy n) (Proxy :: Proxy (IsThisBigOrder n ts)) ts

-- |

class EachSmallOrder (bigOrder :: Nat) (smallOrders :: [Nat]) ts i where
  eachSmallOrder
    :: Proxy bigOrder
    -- ^ Only fill exactly this big order
    -> Proxy smallOrders
    -- ^ These are all the small order to go through.
    -> ts
    -- ^ set of tables.
    -> i
    -- ^ index to update.
    -> ST s ()

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
  ) => EachSmallOrder bigOrder (s ': so) ts i where
  {-# Inline eachSmallOrder #-}
  eachSmallOrder Proxy Proxy ts i = do
    -- fill all tables that have the same big & small order
    thisSmallOrder (Proxy :: Proxy bigOrder) (Proxy :: Proxy s) (Proxy :: Proxy isThisOrder) ts i
    -- fill tables with the next small order
    eachSmallOrder (Proxy :: Proxy bigOrder) (Proxy :: Proxy so) ts i

-- |

class ThisSmallOrder (bigNat :: Nat) (smallNat :: Nat) (thisOrder :: Bool) ts i where
  thisSmallOrder :: Proxy bigNat -> Proxy smallNat -> Proxy thisOrder -> ts -> i -> ST s ()

instance ThisSmallOrder b s any Z i where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder _ _ _ _ _ = return ()

instance
  ( isThisBigOrder ~ IsThisBigOrder bigOrder ts
  , isThisSmallOrder ~ IsThisSmallOrder smallOrder ts
  , isThisOrder ~ (isThisBigOrder && isThisSmallOrder)
  , ThisSmallOrder bigOrder smallOrder isThisOrder ts i
  ) => ThisSmallOrder bigOrder smallOrder 'False (ts:.t) i where
  {-# Inline thisSmallOrder #-}
  -- TODO eta-reduced, does this destroy performance?
  thisSmallOrder Proxy Proxy Proxy (ts:.t) = thisSmallOrder (Proxy :: Proxy bigOrder) (Proxy :: Proxy smallOrder) (Proxy :: Proxy isThisOrder) ts

class IndexConversion gi i where
  convertIndex :: gi -> Maybe i

-- | This instance fills only dense tables. Sparse tables will use a slightly different system,
-- where writes may fail silently!
--
-- TODO generalize from @Id@ to any monad in a stack with a primitive base

instance
  ( PrimArrayOps (Dense v) i x
  , isThisBigOrder ~ IsThisBigOrder bigOrder ts
  , isThisSmallOrder ~ IsThisSmallOrder smallOrder ts
  , isThisOrder ~ (isThisBigOrder && isThisSmallOrder)
  , ThisSmallOrder bigOrder smallOrder isThisOrder ts gi
  , IndexConversion gi i
  ) => ThisSmallOrder bigOrder smallOrder 'True (ts:.TwITbl bo so Id (Dense v) c i x) gi where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder Proxy Proxy Proxy (ts:.TW (ITbl _ arr) f) gi = do
    let uB = upperBound arr
    marr <- unsafeThawM arr
    case convertIndex gi of
      Nothing -> return ()
      Just i  -> do
        z <- return . unId $ inline f uB i
        writeM marr i z
    -- TODO need to write test case that checks that all tables are always filled
    thisSmallOrder (Proxy :: Proxy bigOrder) (Proxy :: Proxy smallOrder) (Proxy :: Proxy isThisOrder) ts gi

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
  ) => ThisSmallOrder bigOrder smallOrder 'True (ts:.TwITbl bo so Id (PAS.Sparse ixw v) c i x) i where
  {-# Inline thisSmallOrder #-}
  thisSmallOrder Proxy Proxy Proxy (ts:.TW (ITbl _ arr) f) i = do
    let uB = upperBound arr
    marr <- unsafeThawM arr
    z <- return . unId $ inline f uB i
    safeWriteM marr i z
    -- TODO need to write test case that checks that all tables are always filled
    thisSmallOrder (Proxy :: Proxy bigOrder) (Proxy :: Proxy smallOrder) (Proxy :: Proxy isThisOrder) ts i




-- | The set of arrays to fill is a tuple of the form @(Z:.a:.b:.c)@. Here, we
-- extract the big order @Nat@s. The set of @Nat@s being returned is already
-- ordered with the smallest @Nat@ up front.

type BigOrderNats arr = Nub (Sort (BigOrderNats' arr))

type family BigOrderNats' arr :: [Nat]

type instance BigOrderNats' Z = '[]

type instance BigOrderNats' (ts:.TwITbl bo so m arr c i x) = bo ': BigOrderNats' ts



type family IsThisBigOrder (n :: Nat) arr :: Bool

type instance IsThisBigOrder n Z = 'False

type instance IsThisBigOrder n (ts:.TwITbl bo so m arr c i x) = n == bo



type SmallOrderNats arr = Nub (Sort (SmallOrderNats' arr))

type family SmallOrderNats' arr :: [Nat]

type instance SmallOrderNats' Z = '[]

-- TODO fix small order

type instance SmallOrderNats' (ts:.TwITbl bo so m arr c i x) = so ': SmallOrderNats' ts



type family IsThisSmallOrder (n :: Nat) arr :: Bool

type instance IsThisSmallOrder n Z = 'False

-- TODO fix small order comparision

type instance IsThisSmallOrder n (ts:.TwITbl bo so m arr c i x) = n == so

data Mutated ts = Mutated
  { mutatedTables       :: ts
  , perfCounter         :: PerfCounter
  , eachBigPerfCounter  :: [PerfCounter]
  }
  deriving (Eq,Ord,Show,Generic)

instance NFData ts => NFData (Mutated ts)

data PerfCounter = PerfCounter
  { picoSeconds   :: !Integer
  , seconds       :: !Double
  , numberOfCells :: !Integer
  }
  deriving (Eq,Ord,Show,Generic)

instance NFData PerfCounter

showPerfCounter :: PerfCounter -> String
{-# NoInline showPerfCounter #-}
showPerfCounter PerfCounter{..} =
  let cellsSecond = round $ fromIntegral numberOfCells / seconds
      m :: Integer = 1000000
  in  printf "%.4f seconds, %d,%06d cells @ %d,%06d cells/second"
             seconds
             (numberOfCells `div` m) (numberOfCells `mod` m)
             (cellsSecond `div` m) (cellsSecond `mod` m)

-- | Semigroup of PerfCounter's just adds up numbers.

instance Semigroup PerfCounter where
  PerfCounter p1 s1 n1 <> PerfCounter p2 s2 n2 = PerfCounter (p1+p2) (s1+s2) (n1+n2)


class CountNumberOfCells (n :: Nat) t where
  countNumberOfCells :: Maybe (Proxy n) -> t -> Integer

instance CountNumberOfCells n Z where
  {-# NoInline countNumberOfCells #-}
  countNumberOfCells p Z = 0

instance
  ( CountNumberOfCells n ts
  , Index i
  , PrimArrayOps arr i x
  , KnownNat n
  , KnownNat bo
  ) => CountNumberOfCells n (ts:.TwITbl bo so Id arr c i x) where
  {-# NoInline countNumberOfCells #-}
  countNumberOfCells mayP (ts:.(TW (ITbl _ arr) fun)) =
    let n  = natVal (Proxy :: Proxy n)
        bo = natVal (Proxy :: Proxy bo)
        cs = countNumberOfCells mayP ts
        c  = product . totalSize $ upperBound arr
    in  case mayP of
      Nothing -> cs + c
      Just _  -> cs + if n==bo then c else 0

