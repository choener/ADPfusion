
module ADP.Fusion.SynVar.Fill where

import           Control.Monad.Morph (hoist, MFunctor (..))
import           Control.Monad.Primitive (PrimMonad (..))
import           Control.Monad.ST
import           Control.Monad.Trans.Class (lift, MonadTrans (..))
import           Data.Vector.Fusion.Util (Id(..))
import           GHC.Exts (inline)
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import           System.IO.Unsafe
import           Control.Monad (when,forM_)
import           Data.List (nub,sort)
import qualified Data.Vector.Unboxed as VU
import           Data.Proxy

import           Data.PrimitiveArray

import           ADP.Fusion.SynVar.Array -- TODO we want to keep only classes in here, move instances to the corresponding modules
import           ADP.Fusion.SynVar.Recursive

import           Debug.Trace



-- * Specialized table-filling wrapper for 'MTbl's
--
-- TODO table-filling does /not/ work for single-dimensional stuff

-- | Run and freeze 'MTbl's. Since actually running the table-filling part
-- is usually the last thing to do, we can freeze as well.

runFreezeMTbls ts = do
    unsafeRunFillTables $ expose ts
    freezeTables        $ onlyTables ts
{-# INLINE runFreezeMTbls #-}



-- * Expose inner mutable tables

-- | Expose the actual mutable table with an 'MTbl'. (Should be temporary
-- until 'MTbl's get a more thorough treatment for auto-filling.

class ExposeTables t where
    type TableFun t   :: *
    type OnlyTables t :: *
    expose     :: t -> TableFun t
    onlyTables :: t -> OnlyTables t

instance ExposeTables Z where
    type TableFun Z   = Z
    type OnlyTables Z = Z
    expose     Z = Z
    onlyTables Z = Z
    {-# INLINE expose #-}
    {-# INLINE onlyTables #-}



-- | A vanilla context-free grammar

data CFG

-- | This grammar is a multi-cfg in a monotone setting

data MonotoneMCFG


-- * Unsafely mutate 'ITbls' and similar tables in the forward phase.

-- | Mutate a cell in a stack of syntactic variables.
--
-- TODO generalize to monad morphism via @mmorph@ package. This will allow
-- more interesting @mrph@ functions that can, for example, track some
-- state in the forward phase. (Note that this can be dangerous, we do
-- /not/ want to have this state influence forward results, unless that can
-- be made deterministic, or we'll break Bellman)

class MutateCell (h :: *) (s :: *) (im :: * -> *) (om :: * -> *) i where
  mutateCell :: Proxy h -> Int -> Int -> (forall a . im a -> om a) -> s -> i -> i -> om ()

-- |

class MutateTables (h :: *) (s :: *) (im :: * -> *) (om :: * -> *) where
  mutateTables :: Proxy h -> (forall a . im a -> om a) -> s -> om s

class TableOrder (s :: *) where
  tableLittleOrder :: s -> [Int]
  tableBigOrder :: s -> [Int]

instance TableOrder Z where
  tableLittleOrder Z = []
  tableBigOrder Z = []
  {-# Inline tableLittleOrder #-}
  {-# Inline tableBigOrder #-}

instance (TableOrder ts) => TableOrder (ts:.ITbl im arr c i x) where
  tableLittleOrder (ts:.ITbl _ tlo _ _ _) = tlo : tableLittleOrder ts
  tableBigOrder    (ts:.ITbl tbo _ _ _ _) = tbo : tableBigOrder ts
  {-# Inline tableLittleOrder #-}
  {-# Inline tableBigOrder #-}

-- | @IRec@s do not need an order, given that they do not memoize.

instance (TableOrder ts) => TableOrder (ts:.IRec im c i x) where
  tableLittleOrder (ts:._) = tableLittleOrder ts
  tableBigOrder    (ts:._) = tableBigOrder ts
  {-# Inline tableLittleOrder #-}
  {-# Inline tableBigOrder #-}

-- ** individual instances for filling a *single cell*

instance
  ( MutateCell CFG ts im om i
  , PrimMonad om
  ) => MutateCell CFG (ts:.IRec im c i x) im om i where
  mutateCell h bo lo mrph (ts:._) lu i = do
    mutateCell h bo lo mrph ts lu i
  {-# Inline mutateCell #-}

instance
  ( PrimArrayOps  arr i x
  , MPrimArrayOps arr i x
  , MutateCell CFG ts im om i
  , PrimMonad om
--  , Show x, Show i
  ) => MutateCell CFG (ts:.ITbl im arr c i x) im om i where
  mutateCell h bo lo mrph (ts:.ITbl tbo tlo c arr f) lu i = do
    mutateCell h bo lo mrph ts lu i
    when (bo==tbo && lo==tlo) $ do
      marr <- unsafeThaw arr
      z <- (inline mrph) $ f lu i
      writeM marr i z
  {-# INLINE mutateCell #-}

type ZS2 = Z:.Subword I:.Subword I

instance
  ( PrimArrayOps  arr ZS2 x
  , MPrimArrayOps arr ZS2 x
  , MutateCell MonotoneMCFG ts im om ZS2
  , PrimMonad om
  ) => MutateCell MonotoneMCFG (ts:.ITbl im arr c ZS2 x) im om ZS2 where
  mutateCell h bo lo mrph (ts:.ITbl tbo tlo c arr f) lu iklj@(Z:.Subword (i:.k):.Subword(l:.j)) = do
    mutateCell h bo lo mrph ts lu iklj
    when (bo==tbo && lo==tlo && k<=l) $ do
      marr <- unsafeThaw arr
      z <- (inline mrph) $ f lu iklj
      writeM marr iklj z
  {-# INLINE mutateCell #-}

instance
  ( PrimArrayOps arr (Subword I) x
  , MPrimArrayOps arr (Subword I) x
  , MutateCell h ts im om (Z:.Subword I:.Subword I)
  , PrimMonad om
  ) => MutateCell h (ts:.ITbl im arr c (Subword I) x) im om (Z:.Subword I:.Subword I) where
  mutateCell h bo lo mrph (ts:.ITbl tbo tlo c arr f) lu@(Z:.Subword (l:._):.Subword(_:.u)) ix@(Z:.Subword (i1:.j1):.Subword (i2:.j2)) = do
    mutateCell h bo lo mrph ts lu ix
    when (bo==tbo && lo==tlo && i1==i2 && j1==j2) $ do
      let i = i1
      let j = j1
      marr <- unsafeThaw arr
      z <- (inline mrph) $ f (subword l u) (subword i j)
      writeM marr (subword i j) z
  {-# Inline mutateCell #-}



-- ** individual instances for filling a complete table and extracting the
-- bounds

instance
  ( Monad om
  , MutateCell h (ts:.ITbl im arr c i x) im om i
  , PrimArrayOps arr i x
  , Show i
  , IndexStream i
  , TableOrder (ts:.ITbl im arr c i x)
  ) => MutateTables h (ts:.ITbl im arr c i x) im om where
  mutateTables h mrph tt@(_:.ITbl _ _ _ arr _) = do
    let (from,to) = bounds arr
    -- TODO (1) find the set of orders for the synvars
    let !tbos = VU.fromList . nub . sort $ tableBigOrder tt
    let !tlos = VU.fromList . nub . sort $ tableLittleOrder tt
    VU.forM_ tbos $ \bo ->
      flip SM.mapM_ (streamUp from to) $ \k ->
        VU.forM_ tlos $ \lo ->
          --traceShow (bo,k,lo) $
          mutateCell h bo lo (inline mrph) tt to k
    return tt
  {-# INLINE mutateTables #-}

instance
  ( Monad om
  ) => MutateCell p Z im om i where
  mutateCell _ _ _ _ Z _ _ = return ()
  {-# INLINE mutateCell #-}

-- | Default table filling, assuming that the forward monad is just @IO@.
--
-- TODO generalize to @MonadIO@ or @MonadPrim@.

mutateTablesDefault :: MutateTables CFG t Id IO => t -> t
mutateTablesDefault t = unsafePerformIO $ mutateTables (Proxy :: Proxy CFG) (return . unId) t
{-# INLINE mutateTablesDefault #-}

-- | Mutate tables, but observe certain hints. We use this for monotone
-- mcfgs for now.

mutateTablesWithHints :: MutateTables h t Id IO => Proxy h -> t -> t
mutateTablesWithHints h t = unsafePerformIO $ mutateTables h (return . unId) t

