
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

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

import           Data.PrimitiveArray

import           ADP.Fusion.SynVar.Array -- TODO we want to keep only classes in here, move instances to the corresponding modules

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

-- Thanks to the table being a gadt we now the internal types
--
-- TODO move to Table/Array.hs

--instance (ExposeTables ts) => ExposeTables (ts:.(MTbl m arr i x)) where
--    type TableFun   (ts:. MTbl m arr i x) = TableFun   ts :. (PA.MutArr m (arr i x), i -> m x)
--    type OnlyTables (ts:. MTbl m arr i x) = OnlyTables ts :. (PA.MutArr m (arr i x))
--    expose     (ts:.MTbl _ t f) = expose ts :. (t,f)
--    onlyTables (ts:.MTbl _ t _) = onlyTables ts :. t
--    {-# INLINE expose #-}
--    {-# INLINE onlyTables #-}



-- * Unsafely mutate 'ITbls' and similar tables in the forward phase.

-- | Mutate a cell in a stack of syntactic variables.
--
-- TODO generalize to monad morphism via @mmorph@ package. This will allow
-- more interesting @mrph@ functions that can, for example, track some
-- state in the forward phase. (Note that this can be dangerous, we do
-- /not/ want to have this state influence forward results, unless that can
-- be made deterministic, or we'll break Bellman)

class MutateCell (s :: *) (im :: * -> *) (om :: * -> *) i where
  mutateCell :: Int -> Int -> (forall a . im a -> om a) -> s -> i -> i -> om ()

-- |

class MutateTables (s :: *) (im :: * -> *) (om :: * -> *) where
  mutateTables :: (forall a . im a -> om a) -> s -> om s

class TableOrder (s :: *) where
  tableLittleOrder :: s -> [Int]
  tableBigOrder :: s -> [Int]

instance TableOrder Z where
  tableLittleOrder Z = []
  tableBigOrder Z = []
  {-# Inline tableLittleOrder #-}
  {-# Inline tableBigOrder #-}

instance (TableOrder ts) => TableOrder (ts:.ITbl im arr i x) where
  tableLittleOrder (ts:.ITbl _ tlo _ _ _) = tlo : tableLittleOrder ts
  tableBigOrder    (ts:.ITbl tbo _ _ _ _) = tbo : tableBigOrder ts
  {-# Inline tableLittleOrder #-}
  {-# Inline tableBigOrder #-}

-- ** individual instances for filling a *single cell*

instance
  ( PrimArrayOps  arr i x
  , MPrimArrayOps arr i x
  , MutateCell ts im om i
  , PrimMonad om
  , Show x, Show i
  ) => MutateCell (ts:.ITbl im arr i x) im om i where
  mutateCell bo lo mrph (ts:.ITbl tbo tlo c arr f) lu i = do
    mutateCell bo lo mrph ts lu i
    when (bo==tbo && lo==tlo) $ do
      marr <- unsafeThaw arr
      z <- (inline mrph) $ f lu i
      writeM marr i z
  {-# INLINE mutateCell #-}

{-
instance
  ( MutateCell ts im om i
  ) => MutateCell (ts:.IRec im i x) im om i where
  mutateCell mrph (ts:.IRec (!c) _ _ f) lu i = do
    mutateCell mrph ts lu i
  {-# INLINE mutateCell #-}
-}

-- ** individual instances for filling a complete table and extracting the
-- bounds

instance
  ( Monad om
  , MutateCell (ts:.ITbl im arr i x) im om i
  , PrimArrayOps arr i x
  , Show i
  , IndexStream i
  , TableOrder (ts:.ITbl im arr i x)
  ) => MutateTables (ts:.ITbl im arr i x) im om where
  mutateTables mrph tt@(_:.ITbl _ _ _ arr _) = do
    let (from,to) = bounds arr
    -- TODO (1) find the set of orders for the synvars
    let !tbos = VU.fromList . nub . sort $ tableBigOrder tt
    let !tlos = VU.fromList . nub . sort $ tableLittleOrder tt
    VU.forM_ tbos $ \bo ->
      flip SM.mapM_ (streamUp from to) $ \k ->
        VU.forM_ tlos $ \lo ->
          mutateCell bo lo (inline mrph) tt to k
    return tt
  {-# INLINE mutateTables #-}

{-
instance
  ( Monad om
  , MutateCell (ts:.IRec im i x) im om i
  , IndexStream i
  ) => MutateTables (ts:.IRec im i x) im om where
  mutateTables mrph tt@(_:.IRec _ from to _) = do
    -- SM.mapM_ (mutateCell (inline mrph) tt to) $ PA.rangeStream from to
    SM.mapM_ (mutateCell (inline mrph) tt to) $ PA.streamUp from to
    return tt
  {-# INLINE mutateTables #-}
-}

instance
  ( Monad om
  ) => MutateCell Z im om i where
  mutateCell _ _ _ Z _ _ = return ()
  {-# INLINE mutateCell #-}

-- | Default table filling, assuming that the forward monad is just @IO@.
--
-- TODO generalize to @MonadIO@ or @MonadPrim@.

mutateTablesDefault :: MutateTables t Id IO => t -> t
mutateTablesDefault t = unsafePerformIO $ mutateTables (return . unId) t
{-# INLINE mutateTablesDefault #-}

