
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
  mutateCell :: (forall a . im a -> om a) -> s -> i -> i -> om ()

-- |

class MutateTables (s :: *) (im :: * -> *) (om :: * -> *) where
  mutateTables :: (forall a . im a -> om a) -> s -> om s

-- ** individual instances for filling a *single cell*

instance
  ( PrimArrayOps  arr i x
  , MPrimArrayOps arr i x
  , MutateCell ts im om i
  , PrimMonad om
  , Show x, Show i
  ) => MutateCell (ts:.ITbl im arr i x) im om i where
  mutateCell mrph (ts:.ITbl c arr f) lu i = do
    mutateCell mrph ts lu i
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
  ) => MutateTables (ts:.ITbl im arr i x) im om where
  mutateTables mrph tt@(_:.ITbl _ arr _) = do
    let (from,to) = bounds arr
    -- SM.mapM_ (mutateCell (inline mrph) tt to) $ PA.rangeStream from to -- TODO check the @to@ part
    SM.mapM_ (mutateCell (inline mrph) tt to) $ streamUp from to -- TODO check the @to@ part
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
  mutateCell _ Z _ _ = return ()
  {-# INLINE mutateCell #-}

-- | Default table filling, assuming that the forward monad is just @IO@.
--
-- TODO generalize to @MonadIO@ or @MonadPrim@.

mutateTablesDefault :: MutateTables t Id IO => t -> t
mutateTablesDefault t = unsafePerformIO $ mutateTables (return . unId) t
{-# INLINE mutateTablesDefault #-}
