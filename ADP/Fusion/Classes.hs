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

import           Data.Array.Repa.Index
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S

import Data.Array.Repa.Index.Points
import Data.Array.Repa.Index.Subword



-- * Data and type constructors

-- | The Inner/Outer handler. We encode three states. We are in 'Outer' or
-- right-most position, or 'Inner' position. The 'Inner' position encodes if
-- loop conditional 'CheckNoCheck' need to be performed.
--
-- In f <<< Z % table % table, the two tables already perform a conditional
-- branch, so that Z/table does not have to check boundary conditions.
--
-- In f <<< Z % table % char, no check is performed in table/char, so Z/table
-- needs to perform a boundary check.

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

-- | @IxStaticVar@ allows us to connect each type of index with variants of
-- @StaticVariable@ stacks. This is important for multi-dimensional grammars,
-- as they have different static/variable behaviour for each dimension.

type family   IxStaticVar ix :: *
type instance IxStaticVar Subword = StaticVariable
type instance IxStaticVar PointL  = StaticVariable
type instance IxStaticVar PointR  = StaticVariable

instance Show StaticVariable where
  show (Static) = "Static"
  show (Variable cb _) = "Variable " ++ show cb

-- | Constrains the behaviour of the memoizing tables. They may be 'EmptyOk' if
-- @i==j@ is allowed (empty subwords or similar); or they may need 'NonEmpty'
-- indices, or finally they can be 'OnlyZero' (only @i==j@ allowed) which is
-- useful in multi-dimensional casese.

data TableConstraint
  = EmptyOk
  | NonEmpty
  | OnlyZero
  deriving (Eq,Show)



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
  mkStream :: x -> IxStaticVar i -> i -> S.Stream m (Elm x i)

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

data S = S

instance
  (
  ) => Element S ix where
  data Elm S ix = ElmS !ix
  type Arg S    = Z
  getArg (ElmS _) = Z
  getIdx (ElmS ix) = ix
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  ) => MkStream m S Subword where
  -- we need to do nothing, because there are no size constraints
  mkStream S (Variable NoCheck Nothing)   (Subword (i:.j)) = S.singleton (ElmS $ subword i i) where
  -- later on, we'd check here if the minimum size requirements can be met (or we can stop early)
  mkStream S (Variable NoCheck (Just ())) (Subword (i:.j)) = error "write me"
  -- in all other cases, we'd better have @i==j@ or this stream stops prematurely
  mkStream S _ (Subword (i:.j)) = S.unfoldr step i where
    {-# INLINE [1] step #-}
    step k
      | k==j      = Just (ElmS $ subword k k, k+1)
      | otherwise = Nothing
  {-# INLINE mkStream #-}



-- * Helper functions

-- | 'staticCheck' acts as a static filter. If 'b' is true, we keep all stream
-- elements. If 'b' is false, we discard all stream elements.

staticCheck :: Monad m => Bool -> S.Stream m a -> S.Stream m a
staticCheck b (S.Stream step t n) = b `seq` S.Stream snew (Left (b:.t)) Unknown where
  {-# INLINE [1] snew #-}
  snew (Left  (False:._)) = return $ S.Done
  snew (Left  (True :.s)) = return $ S.Skip (Right s)
  snew (Right s         ) = do r <- step s
                               case r of
                                 S.Yield x s' -> return $ S.Yield x (Right s')
                                 S.Skip    s' -> return $ S.Skip    (Right s')
                                 S.Done       -> return $ S.Done
{-# INLINE staticCheck #-}

{-
-- |

class Index i where
  type InOut  i :: *
  type ENZ    i :: *
  type PartialIndex i :: *
  type ParserRange i :: *
  outer :: i -> InOut i
  leftPartialIndex  :: i -> PartialIndex i
  rightPartialIndex :: i -> PartialIndex i
  fromPartialIndices :: PartialIndex i -> PartialIndex i -> i

class EmptyENZ enz where
  toEmptyENZ    :: enz -> enz
  toNonEmptyENZ :: enz -> enz

-- | 'ValidIndex', via 'validIndex' statically checks if an index 'i' is valid
-- for a stack of terminals and non-terminals 'x'. 'validIndex' is used to
-- short-circuit streams via 'outerCheck'.

class (Index i) => ValidIndex x i where
  validIndex :: x -> ParserRange i -> i -> Bool
  getParserRange :: x -> i -> ParserRange i



-- * Helper functions

-- | Correct wrapping of 'validIndex' and 'getParserRange'.

checkValidIndex x i = validIndex x (getParserRange x i) i
{-# INLINE checkValidIndex #-}



-- * Instances



-- ** Unsorted

instance EmptyENZ ENE where
  toEmptyENZ ene  | ene==NonEmptyT = EmptyT
                  | otherwise      = ene
  toNonEmptyENZ ene | ene==EmptyT  = NonEmptyT
                    | otherwise    = ene
  {-# INLINE toEmptyENZ #-}
  {-# INLINE toNonEmptyENZ #-}



-- ** PointL

instance Index PointL where
  type InOut PointL = InnerOuter
  type ENZ   PointL = ENE
  type PartialIndex PointL = Int
  type ParserRange  PointL = (Int:!:Int:!:Int)
  outer _ = Outer
  leftPartialIndex (PointL (i:.j)) = i
  rightPartialIndex (PointL (i:.j)) = j
  fromPartialIndices i j = pointL i j
  {-# INLINE outer #-}
  {-# INLINE leftPartialIndex #-}
  {-# INLINE rightPartialIndex #-}
  {-# INLINE fromPartialIndices #-}

instance ValidIndex Z PointL where
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}
  validIndex _ _ _ = True
  getParserRange _ _ = (0 :!: 0 :!: 0)



-- ** 'Subword'

instance Index Subword where
  type InOut Subword = InnerOuter
  type ENZ   Subword = ENE
  type PartialIndex Subword = Int
  type ParserRange Subword = (Int :!: Int :!: Int)
  outer _ = Outer
  leftPartialIndex (Subword (i:.j)) = i
  rightPartialIndex (Subword (i:.j)) = j
  fromPartialIndices i j = subword i j
  {-# INLINE outer #-}
  {-# INLINE leftPartialIndex #-}
  {-# INLINE rightPartialIndex #-}
  {-# INLINE fromPartialIndices #-}

-- | The bottom of every stack of RHS arguments in a grammar.

instance ValidIndex Z Subword where
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}
  validIndex _ _ _ = True
  getParserRange _ _ = (0 :!: 0 :!: 0)



-- ** Outside

instance Index Outside where
  type InOut Outside = InnerOuter
  type ENZ   Outside = ENE
  type PartialIndex Outside = Int
  type ParserRange Outside = (Int :!: Int :!: Int)
  outer _ = Outer
  leftPartialIndex (Outside (i:.j)) = error "outside: not sure yet" -- i
  rightPartialIndex (Outside (i:.j)) = error "outside: not sure yet" -- j
  fromPartialIndices i j = error "outside: not sure yet" -- outside i j
  {-# INLINE outer #-}
  {-# INLINE leftPartialIndex #-}
  {-# INLINE rightPartialIndex #-}
  {-# INLINE fromPartialIndices #-}

-- | The bottom of every stack of RHS arguments in a grammar.

instance
  ( Monad m
  ) => MkStream m Z Outside where
  {-
  mkStream Z Outer !(Outside (i:.j)) = S.unfoldr step i where
    step !k
      | k==j      = P.Just $ (ElmZ (outside i i), j+1)
      | otherwise = P.Nothing
  mkStream Z (Inner NoCheck Nothing)  !(Outside (i:.j)) = S.singleton $ ElmZ $ outside i i
  mkStream Z (Inner NoCheck (Just z)) !(Outside (i:.j)) = S.unfoldr step i where
    step !k
      | k<=j && k+z>=j = P.Just $ (ElmZ (outside i i), j+1)
      | otherwise      = P.Nothing
  mkStream Z (Inner Check Nothing)   !(Outside (i:.j)) = S.unfoldr step i where
    step !k
      | k<=j      = P.Just $ (ElmZ (outside i i), j+1)
      | otherwise = P.Nothing
  mkStream Z (Inner Check (Just z)) !(Outside (i:.j)) = S.unfoldr step i where
    step !k
      | k<=j && k+z>=j = P.Just $ (ElmZ (outside i i), j+1)
      | otherwise      = P.Nothing
  {-# INLINE mkStream #-}
  -}

instance ValidIndex Z Outside where
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}
  validIndex _ _ _ = True
  getParserRange _ _ = (0 :!: 0 :!: 0)



-- ** 'Z'

instance Index Z where
  type InOut Z = Z
  type ENZ   Z = Z
  type PartialIndex Z = Z
  type ParserRange Z = Z
  outer Z = Z
  leftPartialIndex Z = Z
  rightPartialIndex Z = Z
  fromPartialIndices Z Z = Z
  {-# INLINE outer #-}
  {-# INLINE leftPartialIndex #-}
  {-# INLINE rightPartialIndex #-}
  {-# INLINE fromPartialIndices #-}

instance EmptyENZ Z where
  toEmptyENZ _ = Z
  toNonEmptyENZ _ = Z
  {-# INLINE toEmptyENZ #-}
  {-# INLINE toNonEmptyENZ #-}

instance Monad m => MkStream m Z Z where
  mkStream _ _ _ = S.singleton (ElmZ Z)
  {-# INLINE mkStream #-}

instance ValidIndex Z Z where
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}
  validIndex _ _ _ = True
  getParserRange _ _ = Z



-- * Multi-dim instances

-- ** '(is:.i)'

instance (Index is, Index i) => Index (is:.i) where
  type InOut (is:.i) = InOut is :. InOut i
  type ENZ   (is:.i) = ENZ   is :. ENZ i
  type PartialIndex (is:.i) = PartialIndex is :. PartialIndex i
  type ParserRange (is:.i) = ParserRange is :. ParserRange i
  outer (is:.i) = outer is :. outer i
  leftPartialIndex (is:.i) = leftPartialIndex is :. leftPartialIndex i
  rightPartialIndex (is:.i) = rightPartialIndex is :. rightPartialIndex i
  fromPartialIndices (is:.i) (js:.j) = fromPartialIndices is js :. fromPartialIndices i j
  {-# INLINE outer #-}
  {-# INLINE leftPartialIndex #-}
  {-# INLINE rightPartialIndex #-}
  {-# INLINE fromPartialIndices #-}

instance (EmptyENZ es, EmptyENZ e) => EmptyENZ (es:.e) where
  toEmptyENZ (es:.e) = toEmptyENZ es :. toEmptyENZ e
  toNonEmptyENZ (es:.e) = toNonEmptyENZ es :. toNonEmptyENZ e
  {-# INLINE toEmptyENZ #-}
  {-# INLINE toNonEmptyENZ #-}

instance (ValidIndex Z is, ValidIndex Z i) => ValidIndex Z (is:.i) where
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}
  validIndex _ _ _ = True
  getParserRange Z (is:.i) = getParserRange Z is :. getParserRange Z i



-- ** multi-dim with Subword

instance
  ( Monad m
  , MkStream m Z is
  ) => MkStream m Z (is:.Subword) where
  mkStream Z (io:.Outer) (is:.Subword (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.subword i i)) . S.filter (const $ i==j) $ mkStream Z io is
  mkStream Z (io:.Inner NoCheck Nothing) (is:.Subword (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.subword i i)) $ mkStream Z io is
  mkStream Z (io:.Inner NoCheck (Just z)) (is:.Subword (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.subword i i)) . S.filter (const $ i<=j && i+z>=j) $ mkStream Z io is
  mkStream Z (io:.Inner Check Nothing) (is:.Subword (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.subword i i)) . S.filter (const $ i<=j) $ mkStream Z io is
  mkStream Z (io:.Inner Check (Just z)) (is:.Subword (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.subword i i)) . S.filter (const $ i<=j && i+z>=j) $ mkStream Z io is
  {-# INLINE mkStream #-}



-- ** multi-dim with PointL

-- TODO automatically created, check correctness

instance
  ( Monad m
  , MkStream m Z is
  ) => MkStream m Z (is:.PointL) where
  mkStream Z (io:.Outer) (is:.PointL (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.pointL i i)) . S.filter (const $ i==j) $ mkStream Z io is
  mkStream Z (io:.Inner NoCheck Nothing) (is:.PointL (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.pointL i i)) $ mkStream Z io is
  mkStream Z (io:.Inner NoCheck (Just z)) (is:.PointL (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.pointL i i)) . S.filter (const $ i<=j && i+z>=j) $ mkStream Z io is
  mkStream Z (io:.Inner Check Nothing) (is:.PointL (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.pointL i i)) . S.filter (const $ i<=j) $ mkStream Z io is
  mkStream Z (io:.Inner Check (Just z)) (is:.PointL (i:.j))
    = S.map (\(ElmZ jt) -> ElmZ (jt:.pointL i i)) . S.filter (const $ i<=j && i+z>=j) $ mkStream Z io is
  {-# INLINE mkStream #-}





-}
