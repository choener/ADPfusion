{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{- OPTIONS_GHC -funbox-strict-fields #-}

module ADP.Fusion.Classes where

import Control.Monad.Primitive
import Data.Array.Repa.Index
import Data.Primitive.Types (Prim(..))
import Data.Vector.Fusion.Stream.Size
import GHC.Prim (Constraint)
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector as V
import Control.DeepSeq
import GHC.TypeLits

import Debug.Trace



-- * Classes for generalized ADPfusion.

class MkElm x i where
  data Plm x i :: *
  data Elm x i :: *
  type Arg  x :: *
  topIdx :: Elm x i -> Is i
  getArg :: Elm x i -> Arg x

class ({- Index i, -} Monad m) => MkS m x i where
  mkS :: x -> IsT i -> i -> S.Stream m (Elm x i)

-- | Convert 'OIR' and calculate successor indices.
--
-- NOTE You need to implement this class for all symbols and all index types.
-- Alternatively, implement just instances for 'Term' and use the k-dimensional
-- abstraction.

class {- (Index i) => -} Next x i where
  suc :: x -> IsT i -> i -> Is i -> Is i -> Is i
  convT :: x -> IsT i -> IsT i

class Index i where
  data Is i :: *
  data IsT i :: *
  toL :: i -> Is i
  toR :: i -> Is i
  from :: Is i -> Is i -> i
  leftOfR :: Is i -> i -> Bool

class (Monad m) => TEE m x i where
  type TE x :: *
  data TI x i m :: *
  te :: x -> Is i -> Is i -> S.Stream m (TE x)
  ti :: x -> Is i -> Is i -> (TI x i m)
  tisuc :: x -> Is i -> Is i -> TI x i m -> (TI x i m)
  tifin :: TI x i m -> Bool
  tiget :: x -> Is i -> Is i -> TI x i m -> m (TE x)
  tiOne :: x -> Is i -> Is i -> m (TE x)

data OIR
  = Outer
  | Inner
  | Restricted
  deriving (Eq)



-- * basic instances

instance Index Z where
  newtype Is Z = IsZ Bool
  newtype IsT Z = IsTz Z
  toL Z = IsZ True
  toR Z = IsZ True
  from _ _ = Z
  leftOfR (IsZ ft) Z = ft
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance NFData Z where
  rnf Z = ()

instance NFData (Is Z) where
  rnf (IsZ b) = rnf b

instance Index z => Index (z:.Int) where
  newtype Is (z:.Int) = IsInt (Is z:.Int)
  newtype IsT (z:.Int) = IsTint (IsT z :. OIR)
  toL (z:.i) = IsInt $ toL z :. i
  toR (z:.i) = IsInt $ toR z :. i
  from (IsInt (z:.i)) (IsInt (z':._)) = from z z' :. i
  leftOfR (IsInt (z:.i)) (z':.j) = leftOfR z z' -- || i<=j
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance Index z => Index (z:.(Int:.Int)) where
  newtype Is (z:.(Int:.Int)) = IsIntInt (Is z:.Int)
  newtype IsT (z:.(Int:.Int)) = IsTii (IsT z :. OIR)
  toL (z:.(i:.j)) = IsIntInt $ toL z:.i
  toR (z:.(i:.j)) = IsIntInt $ toR z:.j
  from (IsIntInt (z:.i)) (IsIntInt (z':.j)) = from z z' :.(i:.j)
  leftOfR (IsIntInt (z:.k)) (z':.(i:.j)) = leftOfR z z'
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance NFData z => NFData (z:.(Int:.Int)) where
  rnf (z:.(i:.j)) = i `seq` j `seq` rnf z

instance NFData (Is z) => NFData (Is (z:.(Int:.Int))) where
  rnf (IsIntInt (z:.k)) = k `seq` rnf z

