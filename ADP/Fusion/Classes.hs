
module ADP.Fusion.Classes where

import           Data.Bits

import           Data.Bits.Ordered

import Debug.Trace



-- * Data and type constructors

-- | The Inner/Outer handler. We encode three states. We are in 'Outer' or
-- right-most position, or 'Inner' position. The 'Inner' position encodes
-- if loop conditional 'CheckNoCheck' need to be performed.
--
-- In @f <<< Z % table % table@, the two tables already perform
-- a conditional branch, so that Z/table does not have to check boundary
-- conditions.
--
-- In @f <<< Z % table % char@, no check is performed in table/char, so
-- Z/table needs to perform a boundary check.

-- | Signals if we still need to do bounds checking. As long as we have static
-- components, there is the possibility of out-of-bounds errors (once we have
-- at least one 'flatten' that problem is gone). We signal using 'CheckBounds'.

data CheckBounds
  = Check
  | NoCheck
  deriving (Eq,Show)

-- | Depending on if we have a static or a variable part in the element
-- deconstruction, we will have to either work with the static indices coming
-- from the outside, or use the moving indices calculated in in the inner
-- parts.

{-
data StaticVariable v
  = Static
  | Variable CheckBounds (Maybe v) -- TODO type family based on the index type to allow saying if we need maximal sizes further in
  deriving Eq

instance Show v => Show (StaticVariable v) where
  show (Static) = "Static"
  show (Variable cb Nothing) = "Variable " ++ show cb
  show (Variable cb (Just v)) = "Variable " ++ show cb ++ " " ++ show v
-}

-- | 'mkStream' needs to know the current context within the sequence of
-- symbols.

-- | @IxStaticVar@ allows us to connect each type of index with variants of
-- @StaticVariable@ stacks. This is important for multi-dimensional grammars,
-- as they have different static/variable behaviour for each dimension.

{-
class IxStaticVar i where
  type IxSV ix :: *
  initialSV :: i -> IxSV i

instance IxStaticVar i => IxStaticVar (Outside i) where
  type IxSV (Outside i) = IxSV i
  initialSV (O i) = initialSV i
-}

{-
instance IxStaticVar Subword where
  type IxSV Subword = StaticVariable
  initialSV _ = Static
-}

{-
instance IxStaticVar PointL where
  type IxSV PointL  = StaticVariable ()
  initialSV _ = Static

instance IxStaticVar PointR where
  type IxSV PointR  = StaticVariable ()
  initialSV _ = Static

instance IxStaticVar BitSet where
  type IxSV BitSet = StaticVariable Int
  initialSV _ = Static

instance IxStaticVar (BitSet:>Interface i) where
  type IxSV (BitSet:>Interface i) = StaticVariable Int
  initialSV _ = Static

instance IxStaticVar (BitSet:>Interface i:>Interface j) where
  type IxSV (BitSet:>Interface i:>Interface j) = StaticVariable Int
  initialSV _ = Static
-}

{-
type instance TblConstraint Subword = TableConstraint
-}
type instance TblConstraint PointL  = TableConstraint
type instance TblConstraint PointR  = TableConstraint
type instance TblConstraint BitSet  = TableConstraint
type instance TblConstraint (BitSet:>Interface i)  = TableConstraint
type instance TblConstraint (BitSet:>Interface i:>Interface j)  = TableConstraint

{-
type instance TblConstraint (Outside Subword) = TableConstraint
type instance TblConstraint (Outside PointL)  = TableConstraint
type instance TblConstraint (Outside PointR)  = TableConstraint
-}

-- * The ADPfusion base classes.



-- * Instances for the bottom of the stack. We provide default instances for
-- 'Subword', 'PointL', 'PointR' and the multidimensional variants.

-- | The instance for the bottom of a stack with subwords. In cases where we
-- still need to check correctness of boundaries (i.e. @i==j@ in the
-- bottom-most case), we use a 'staticCheck' which is promoted upward in the
-- recursion and therefore occurs only once, not in every single loop. And
-- neither does it introduce another loop.

{-
instance (Monad m) => MkStream m S Subword where
  -- we need to do nothing, because there are no size constraints
  mkStream S (Variable NoCheck Nothing) _  (Subword (i:.j)) = S.singleton (ElmS $ subword i i)
  -- later on, we'd check here if the minimum size requirements can be met (or we can stop early)
  mkStream S (Variable NoCheck (Just ())) _ (Subword (i:.j)) = error "write me"
  -- once we are variable, but still have to check, we make sure that we have a legal subword, then return the empty subword starting at @i@.
  mkStream S (Variable Check   Nothing) _ (Subword (i:.j)) = staticCheck (i<=j) $ S.singleton (ElmS $ subword i i)
  -- in all other cases, we'd better have @i==j@ or this stream stops prematurely
  mkStream S _ _ (Subword (i:.j)) = staticCheck (i==j) $ S.singleton (ElmS $ subword i i)
  {-# INLINE mkStream #-}

instance (Monad m) => MkStream m S (Outside Subword) where
  -- TODO missing some defn's
  mkStream S (Variable NoCheck Nothing  ) _ (O (Subword (i:.j))) = S.singleton (ElmS . O $ subword i i)
  mkStream S (Variable NoCheck (Just ())) _ _ = error "S2"
  mkStream S (Variable Check   Nothing  ) (O (Subword (l:.u))) (O (Subword (i:.j)))
    = staticCheck (l<=i) $ S.singleton (ElmS . O $ subword i i)
  -- all other cases; but mostly when we have @Static@
  mkStream S _ (O (Subword (l:.u))) (O (Subword (i:.j))) = staticCheck (l==i && u==j) $ S.singleton (ElmS . O $ subword l u)
  {-# INLINE mkStream #-}
-}

{-
instance (Monad m) => MkStream m S (Outside PointL) where
  mkStream S (Variable Check Nothing) (O (PointL (l:.u))) (O (PointL (i:.j)))
    = staticCheck (j>=l && j<=u && i<=j) $ S.singleton (ElmS . O $ PointL (j:.j))
  mkStream S Static (O (PointL (l:.u))) (O (PointL (i:.j)))
    = staticCheck (i==l && u==j) $ S.singleton (ElmS . O $ PointL (i:.j))
--  mkStream S z (O (PointL (l:.u))) (O (PointL (i:.j))) = error $ "S.PointL write me: " ++ show z
  {-# INLINE mkStream #-}
-}

-- TODO need to check these guys

{-
instance (Monad m) => MkStream m S BitSet where
  mkStream S (Variable Check Nothing) (BitSet l) (BitSet h)
    = staticCheck (l<=h) $ S.singleton (ElmS $ BitSet l)
  mkStream S Static (BitSet l) (BitSet h)
    = staticCheck (l==h) $ S.singleton (ElmS $ BitSet l)
  {-# INLINE mkStream #-}

instance (Monad m) => MkStream m S (BitSet:>Interface i) where
  mkStream S (Variable Check Nothing) (BitSet lb:>Interface li) (BitSet hb:>Interface hi)
    = staticCheck (lb<=hb && li <= hi) $ S.singleton (ElmS $ (BitSet lb:>Interface li))
  mkStream S Static (BitSet lb:>Interface li) (BitSet hb:>Interface hi)
    = staticCheck (lb==hb && li==hi) $ S.singleton (ElmS (BitSet lb:>Interface li))
  {-# INLINE mkStream #-}
-}

-- | For bitsets, we do not always return just a singleton case. Whenever
-- we are in the variable case with a moving @Last@ point, more than one
-- returned candidate needs to be generated.

{-
instance (Monad m) => MkStream m S (BitSet:>Interface First:>Interface Last) where
  -- In the static case we should have an empty bitset at this point. In
  -- the stack @(S:.x)@ @x@ is something like @Empty@ or a terminal.
  mkStream S Static _ (BitSet b:>_:>_)
    = staticCheck (b==0) $ S.singleton (ElmS (BitSet b:>Interface 0:>Interface 0))
  -- this one is fun. We first need to calcuate which bits need to be
  -- switched on. Lets say, @popCount cb==3@ and @k==2@. Then we need to
  -- produce all bitsets that are subsets of @cb@ with two active bits. Of
  -- these, @ci@ is fixed as one of the interface bits. The @cj@ interface
  -- is unimportant.
  mkStream S (Variable _ (Just k)) (BitSet zb:>Interface zi:>Interface zj) (BitSet cb:>Interface ci:>_)
    = S.map (\(Z:.(BitSet b:>j)) -> ElmS (BitSet (movePopulation cb b):>Interface ci:>j))
    $ S.filter (\(Z:.(BitSet b:>Interface j)) -> testBit b ci && (popCount b == 1 || ci /= j))
    $ S.takeWhile (\(Z:.(BitSet b:>_)) -> popCount b <= k)
    $ streamUp (Z:.(BitSet (2^k-1):>Interface 0)) (Z:.(BitSet (2^(popCount cb)-1):>Interface 0))
  {-# INLINE mkStream #-}
-}

{-
instance (Monad m) => MkStream m S (BitSet:>Interface i:>Interface j) where
  mkStream S (Variable Check Nothing) (BitSet lb:>Interface li:>Interface lj) (BitSet hb:>Interface hi:>Interface hj)
    = staticCheck (lb<=hb && li <= hi && lj <= hj) $ S.singleton (ElmS (BitSet lb:>Interface li:>Interface lj))
  mkStream S Static (BitSet lb:>Interface li:>Interface lj) (BitSet hb:>Interface hi:>Interface hj)
    = staticCheck (lb==hb && li==hi && lj==hj) $ S.singleton (ElmS (BitSet lb:>Interface li:>Interface lj))
  {-# INLINE mkStream #-}
-}

-- * Helper functions

