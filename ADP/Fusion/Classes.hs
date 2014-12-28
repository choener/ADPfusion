{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module ADP.Fusion.Classes where

import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray (Z(..), (:.)(..), Subword(..), subword, PointL(..), PointR(..), Outside(..))

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

data StaticVariable
  = Static
  | Variable CheckBounds (Maybe ()) -- TODO type family based on the index type to allow saying if we need maximal sizes further in
  deriving Eq

instance Show StaticVariable where
  show (Static) = "Static"
  show (Variable cb _) = "Variable " ++ show cb

-- | @IxStaticVar@ allows us to connect each type of index with variants of
-- @StaticVariable@ stacks. This is important for multi-dimensional grammars,
-- as they have different static/variable behaviour for each dimension.

class IxStaticVar i where
  type IxSV ix :: *
  initialSV :: i -> IxSV i

instance IxStaticVar i => IxStaticVar (Outside i) where
  type IxSV (Outside i) = IxSV i
  initialSV (O i) = initialSV i

instance IxStaticVar Subword where
  type IxSV Subword = StaticVariable
  initialSV _ = Static

instance IxStaticVar PointL where
  type IxSV PointL  = StaticVariable
  initialSV _ = Static

instance IxStaticVar PointR where
  type IxSV PointR  = StaticVariable
  initialSV _ = Static

-- | Constrains the behaviour of the memoizing tables. They may be 'EmptyOk' if
-- @i==j@ is allowed (empty subwords or similar); or they may need 'NonEmpty'
-- indices, or finally they can be 'OnlyZero' (only @i==j@ allowed) which is
-- useful in multi-dimensional casese.

data TableConstraint
  = EmptyOk
  | NonEmpty
  | OnlyZero
  deriving (Eq,Show)

minSize :: TableConstraint -> Int
minSize NonEmpty = 1
minSize _        = 0
{-# INLINE minSize #-}

class ModifyConstraint t where
  toNonEmpty :: t -> t
  toEmpty    :: t -> t

-- |

type family   TblConstraint x       :: *

type instance TblConstraint (is:.i) =  TblConstraint is :. TblConstraint i
type instance TblConstraint Z       = Z
type instance TblConstraint Subword = TableConstraint
type instance TblConstraint PointL  = TableConstraint
type instance TblConstraint PointR  = TableConstraint

type instance TblConstraint (Outside Subword) = TableConstraint
type instance TblConstraint (Outside PointL)  = TableConstraint
type instance TblConstraint (Outside PointR)  = TableConstraint


-- * The ADPfusion base classes.

-- | During construction of the stream, we need to extract individual elements
-- from symbols in production rules. An element in a stream is fixed by both,
-- the type @x@ of the actual argument we want to grab (say individual
-- characters we parse from an input) and the type of indices @i@ we use.
--
-- @Elm@ data constructors are all eradicated during fusion and should never
-- show up in CORE.

class Element x i where
  data Elm x i :: *
  type Arg x :: *
  getArg :: Elm x i -> Arg x
  getIdx :: Elm x i -> i

-- | @mkStream@ creates the actual stream of elements (@Elm@) that will be fed
-- to functions on the left of the @(<<<)@ operator. Streams work over all
-- monads and are specialized for each combination of arguments @x@ and indices
-- @i@.

class (Monad m) => MkStream m x i where
  mkStream :: x -> IxSV i -> i -> i -> S.Stream m (Elm x i)

-- | Finally, we need to be able to correctly build together symbols on the
-- right-hand side of the @(<<<)@ operator.
--
-- The default makes sure that the last (or only) argument left over is
-- correctly assigned a @Z@ to terminate the symbol stack.

class Build x where
  type Stack x :: *
  type Stack x = S :!: x
  build :: x -> Stack x
  default build :: (Stack x ~ (S :!: x)) => x -> Stack x
  build x = S :!: x
  {-# INLINE build #-}

instance Build x => Build (x:!:y) where
  type Stack (x:!:y) = Stack x :!: y
  build (x:!:y) = build x :!: y
  {-# INLINE build #-}



-- * Instances for the bottom of the stack. We provide default instances for
-- 'Subword', 'PointL', 'PointR' and the multidimensional variants.

-- | Similar to 'Z', but terminates an argument stack.

data S = S
  deriving (Eq,Show)

instance
  (
  ) => Element S ix where
  data Elm S ix = ElmS !ix
  type Arg S    = Z
  getArg (ElmS _) = Z
  getIdx (ElmS ix) = ix
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

-- | The instance for the bottom of a stack with subwords. In cases where we
-- still need to check correctness of boundaries (i.e. @i==j@ in the
-- bottom-most case), we use a 'staticCheck' which is promoted upward in the
-- recursion and therefore occurs only once, not in every single loop. And
-- neither does it introduce another loop.

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

instance (Monad m) => MkStream m S PointL where
  mkStream S (Variable Check Nothing) (PointL (l:.u)) (PointL (i:.j))
    = staticCheck (j>=l && j<=u && i<=j) $ S.singleton (ElmS $ PointL (i:.i))
  mkStream S Static (PointL (l:.u)) (PointL (i:.j))
    = staticCheck (i==j) $ S.singleton (ElmS $ PointL (i:.i))
--  mkStream S z (PointL (l:.u)) (PointL (i:.j)) = error $ "S.PointL write me: " ++ show z
  {-# INLINE mkStream #-}

instance (Monad m) => MkStream m S (Outside PointL) where
  mkStream S (Variable Check Nothing) (O (PointL (l:.u))) (O (PointL (i:.j)))
    = staticCheck (j>=l && j<=u && i<=j) $ S.singleton (ElmS . O $ PointL (j:.j))
  mkStream S Static (O (PointL (l:.u))) (O (PointL (i:.j)))
    = staticCheck (i==l && u==j) $ S.singleton (ElmS . O $ PointL (i:.j))
--  mkStream S z (O (PointL (l:.u))) (O (PointL (i:.j))) = error $ "S.PointL write me: " ++ show z
  {-# INLINE mkStream #-}

-- * Helper functions

-- | 'staticCheck' acts as a static filter. If 'b' is true, we keep all stream
-- elements. If 'b' is false, we discard all stream elements.

staticCheck :: Monad m => Bool -> S.Stream m a -> S.Stream m a
staticCheck b (S.Stream step t n) = b `seq` S.Stream snew (Left (b:.t)) (toMax n) where
  {-# INLINE [1] snew #-}
  snew (Left  (False:._)) = return $ S.Done
  snew (Left  (True :.s)) = return $ S.Skip (Right s)
  snew (Right s         ) = do r <- step s
                               case r of
                                 S.Yield x s' -> return $ S.Yield x (Right s')
                                 S.Skip    s' -> return $ S.Skip    (Right s')
                                 S.Done       -> return $ S.Done
{-# INLINE staticCheck #-}

