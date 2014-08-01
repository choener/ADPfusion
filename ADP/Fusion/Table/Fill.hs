{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module ADP.Fusion.Table.Fill where

import           Control.Monad.Primitive (PrimMonad (..))

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

instance (ExposeTables ts) => ExposeTables (ts:.(MTbl m arr i x)) where
    type TableFun   (ts:. MTbl m arr i x) = TableFun   ts :. (PA.MutArr m (arr i x), i -> m x)
    type OnlyTables (ts:. MTbl m arr i x) = OnlyTables ts :. (PA.MutArr m (arr i x))
    expose     (ts:.MTbl _ t f) = expose ts :. (t,f)
    onlyTables (ts:.MTbl _ t _) = onlyTables ts :. t
    {-# INLINE expose #-}
    {-# INLINE onlyTables #-}

