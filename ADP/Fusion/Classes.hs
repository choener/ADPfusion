{-# LANGUAGE DefaultSignatures #-}
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

-- | Generalized ADPfusion.
--
-- Some useful rules:
--
-- - if you invent a new index type, always write it using a "newtype", never
-- implement in terms of standard data constructors.

module ADP.Fusion.Classes where

import Control.DeepSeq
import Control.Monad.Primitive
import Data.Array.Repa.Index
import Data.Primitive.Types (Prim(..))
import Data.Vector.Fusion.Stream.Monadic (Stream(..))
import Data.Vector.Fusion.Stream.Size
import GHC.Prim (Constraint)
import GHC.TypeLits
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU

import Data.Array.Repa.Index.Subword



-- * Classes for generalized ADPfusion.

-- | Individual elements of a fusionable stream.

class StreamElm x i where
  -- | an individual element (and index information)
  data Elm x i :: *
  -- | the argument stack for function application
  type Arg x   :: *
  -- | get the "right" index part of the element we have created. Typically
  -- used in mkStream to get the right-most index of the left part of the
  -- production we are in
  getIxP :: Elm x i -> IxP i
  -- | get the arguments as an argument stack
  getArg :: Elm x i -> Arg x

-- | Create a stream 

class (Monad m) => MkStream m x i where
  -- | Create a stream from a symbol 'x', the type 'IxT i' of the index (outer
  -- / inner / special), and the index 'i'.
  mkStream :: x -> IxT i -> i -> Stream m (Elm x i)

-- | Convert 'OIR' and calculate successor indices.
--
-- NOTE You need to implement this class for all symbols and all index types.
-- Alternatively, implement just instances for 'Term' and use the k-dimensional
-- abstraction.

class Next x i where
  -- | Create the initial index to start with. If we have, say, a non-empty
  -- table, it will advance the initial index by one.
  initP :: x -> IxT i -> i -> IxP i -> IxP i
  -- | Given the symbol 'x', the index type 'IxT i', the global index 'i', and
  -- the left and right constraints of our local subword 'IxP i', create the
  -- next step. This basically moves our index by one.
  nextP :: x -> IxT i -> i -> IxP i -> IxP i -> IxP i
  -- | More complicated stopping function. Stopping depends on symbol and
  -- index.
  --
  -- TODO should replace 'leftOfR'
  doneP :: x -> IxT i -> i -> IxP i -> Bool
  -- | Convert the index type and maybe change the index itself. Used by, for
  -- example, the single-character parser to reduce the right-most index in 'i'
  -- by one.
  convT :: x -> IxT i -> i -> (IxT i, i)

-- | index calculations.
--
-- For an index 'i', we have a partial index type 'IxP' which denotes the
-- "borders" of an index. For a subword (i,j), the index part would we single
-- Int, say, "j".
--
-- The index type 'IxT' constrains the index further. We want to wrap the 'OIR'
-- data type to specialize 'mkStream' in certain cases like the right-most
-- symbol in a production rule.

class Index i where
  -- | Partial index. Is the left or right "border" of an index 'i'.
  data IxP i :: *
  -- | The type of an index. Wraps 'OIR' for each dimension.
  data IxT i :: *
  -- | Extracts the left border of an index.
  toL :: i -> IxP i
  -- | Extracts the right border of an index.
  toR :: i -> IxP i
  -- | Compose two partial indices into one complete one.
  from :: IxP i -> IxP i -> i
  -- | Ask if a partial index is to the left of the right part of an index.
  --
  -- TODO maybe "leftOfR :: IxP i -> IxP i -> Bool" ?
  leftOfR :: IxP i -> i -> Bool
  -- simplify IxT stuff by providing a default
  initT :: IxT i

-- | Standard cases on how 'mkStream' can be restricted. In the 'Outer' case,
-- we perform a single step, then finish. The 'Inner' case behaves normally,
-- while 'Restricted' is used for special symbols.
--
-- TODO implemented 'Restricted' correctly.

data OIR i
  = Outer
  | Inner
  | Restrict -- !(Maybe i) !(Maybe i)
  deriving (Eq,Show)

instance NFData (OIR i) where
  rnf !x = ()

-- | Access an element, given partial indices. Note that we return in a monad.

class (Monad m) => Element m x i where
  -- | The type of the element of 'x' that we return.
  type E x :: *
  -- | Get the element given symbol, and two partial indices.
  getE :: x -> IxP i -> IxP i -> m (E x)

-- | A class handling terminal elements. In the multi-dimensional case,
-- terminal symbols are much more complex as each individual element could be
-- constrained, steps differently, or more.
--
-- TODO requires overhaul!

class (Monad m) => TermElement m x i where
  type TermElm x :: *
  data TermIx x i m :: *
  te :: x -> IxP i -> IxP i -> S.Stream m (TermElm x)
  ti :: x -> IxP i -> IxP i -> (TermIx x i m)
  tisuc :: x -> IxP i -> IxP i -> TermIx x i m -> (TermIx x i m)
  tifin :: TermIx x i m -> Bool
  tiget :: x -> IxP i -> IxP i -> TermIx x i m -> m (TermElm x)
  tiOne :: x -> IxP i -> IxP i -> m (TermElm x)




instance Index Subword where
  newtype IxP Subword = IxPsubword Int
  newtype IxT Subword = IxTsubword (OIR (IxP Subword))
  toL (Subword (i:.j)) = IxPsubword i
  toR (Subword (i:.j)) = IxPsubword j
  from (IxPsubword i) (IxPsubword j) = Subword (i:.j)
  leftOfR (IxPsubword k) (Subword (i:.j)) = k<=j
  initT = IxTsubword Outer
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}
  {-# INLINE initT #-}

instance NFData (IxP Subword) where
  rnf (IxPsubword i) = rnf i

instance NFData (IxT Subword) where
  rnf (IxTsubword oir) = rnf oir

deriving instance Show (IxP Subword)

deriving instance Eq (IxP Subword)

deriving instance Show (IxT Subword)

{-

-- * basic instances

instance Index Z where
  newtype IxP Z = IxPZ Bool
  newtype IxPT Z = IxPTz Z
  toL Z = IxPZ True
  toR Z = IxPZ True
  from _ _ = Z
  leftOfR (IxPZ ft) Z = ft
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance NFData Z where
  rnf Z = ()

instance NFData (IxP Z) where
  rnf (IxPZ b) = rnf b

instance Index z => Index (z:.Int) where
  newtype IxP (z:.Int) = IxPInt (IxP z:.Int)
  newtype IxPT (z:.Int) = IxPTint (IxPT z :. OIR)
  toL (z:.i) = IxPInt $ toL z :. i
  toR (z:.i) = IxPInt $ toR z :. i
  from (IxPInt (z:.i)) (IxPInt (z':._)) = from z z' :. i
  leftOfR (IxPInt (z:.i)) (z':.j) = leftOfR z z' -- || i<=j
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance Index z => Index (z:.(Int:.Int)) where
  newtype IxP (z:.(Int:.Int)) = IxPIntInt (IxP z:.Int)
  newtype IxPT (z:.(Int:.Int)) = IxPTii (IxPT z :. OIR)
  toL (z:.(i:.j)) = IxPIntInt $ toL z:.i
  toR (z:.(i:.j)) = IxPIntInt $ toR z:.j
  from (IxPIntInt (z:.i)) (IxPIntInt (z':.j)) = from z z' :.(i:.j)
  leftOfR (IxPIntInt (z:.k)) (z':.(i:.j)) = leftOfR z z'
  {-# INLINE toL #-}
  {-# INLINE toR #-}
  {-# INLINE from #-}
  {-# INLINE leftOfR #-}

instance NFData z => NFData (z:.(Int:.Int)) where
  rnf (z:.(i:.j)) = i `seq` j `seq` rnf z

instance NFData (IxP z) => NFData (IxP (z:.(Int:.Int))) where
  rnf (IxPIntInt (z:.k)) = k `seq` rnf z
-}

-- | Build the stack using (%)

class Build x where
  type Stack x :: *
  type Stack x = None :. x
  build :: x -> Stack x
  default build :: (Stack x ~ (None :. x)) => x -> Stack x
  build x = None :. x
  {-# INLINE build #-}

instance Build x => Build (x:.y) where
  type Stack (x:.y) = Stack x :. y
  build (x:.y) = build x :. y
  {-# INLINE build #-}

data None = None

instance
  ( NFData (IxP i)
  ) => StreamElm None i where
  data Elm None i = ElmNone (IxP i)
  type Arg None = Z
  getIxP (ElmNone k) = k
  getArg (ElmNone i) = i `deepseq` Z
  {-# INLINE getIxP #-}
  {-# INLINE getArg #-}

instance (Monad m) => MkStream m None Subword where
--  mkStream None ox ix = let k = toL ix in (ox,ix,k) `deepseq` S.singleton (ElmNone k)
  mkStream None ox ix@(Subword (i:.j)) = (ox,ix,k) `deepseq` S.unfoldr step (i<=j) where
    k = toL ix
    step b
      | b = Just (ElmNone k, False)
      | otherwise = Nothing
    {-# INLINE step #-}
  {-# INLINE mkStream #-}

instance (NFData (IxP i)) => NFData (Elm None i) where
  rnf (ElmNone i) = rnf i

instance NFData None where
  rnf None = ()

deriving instance (Show (IxP i)) => Show (Elm None i)

