{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module ADP.Fusion.Table.Fill where

import           Control.Monad.Primitive (PrimMonad (..))
import           Control.Monad.Morph (hoist, MFunctor (..))
import           Control.Monad.Trans.Class (lift, MonadTrans (..))

import           Data.PrimitiveArray (Z(..), (:.)(..))
import qualified Data.PrimitiveArray as PA

import           ADP.Fusion.Table



-- * Specialized table-filling wrapper for 'MTbl's
--
-- TODO table-filling does /not/ work for single-dimensional stuff

-- | Run and freeze 'MTbl's. Since actually running the table-filling part
-- is usually the last thing to do, we can freeze as well.

runFreezeMTbls ts = do
    PA.unsafeRunFillTables $ expose ts
    PA.freezeTables        $ onlyTables ts
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

instance (ExposeTables ts) => ExposeTables (ts:.(MTbl m arr i x)) where
    type TableFun   (ts:. MTbl m arr i x) = TableFun   ts :. (PA.MutArr m (arr i x), i -> m x)
    type OnlyTables (ts:. MTbl m arr i x) = OnlyTables ts :. (PA.MutArr m (arr i x))
    expose     (ts:.MTbl _ t f) = expose ts :. (t,f)
    onlyTables (ts:.MTbl _ t _) = onlyTables ts :. t
    {-# INLINE expose #-}
    {-# INLINE onlyTables #-}



-- * Unsafely mutate 'ITbls' and similar tables in the forward phase.

-- | Mutate a cell in a stack of syntactic variables.
--
-- NOTE the index @i@ is separate from the table (stack) @t@ as we might
-- have special cases where @i@ is different from the indices in @t@.

class MutateCell s where
  type MM s :: * -> * -- The monad used to perform the forward calculations in (probably @Identity@)
  mutateCell :: (Monad (MM s), Monad n, PrimMonad n, Monad (t n), MonadTrans t, MFunctor t) => (forall a . (MM s) a -> n a) -> s -> (forall i . i) -> t n ()

instance
  ( PA.PrimArrayOps  arr i x
  , PA.MPrimArrayOps arr i x
  ) => MutateCell (ITbl m arr i x) where
  type MM (ITbl m arr i x) = m
  mutateCell mmorph (ITbl _ arr f) i = do
    marr <- lift $ PA.unsafeThaw arr
    z <- hoist mmorph (lift $ f i)
    lift $ PA.writeM marr i z
    return ()
  {-# INLINE mutateCell #-}

class MutateStack s where
  mutateStackCell :: (MFunctor t, MonadTrans t, PrimMonad n, Monad (t n)) => (forall a . (MM s) a -> n a) -> s -> (forall i . i) -> t n ()

instance
  ( MutateCell t
  , Monad (MM t)
  ) => MutateStack (ts:.t) where
  mutateStackCell mmorph (ts:.t) i = mutateCell mmorph t i -- mutateStackCell mmorph ts i >> mutateCell mmorph t i

