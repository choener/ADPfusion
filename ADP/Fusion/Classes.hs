{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module ADP.Fusion.Classes where

import Data.Array.Repa.Index
import Data.Strict.Maybe
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Size
import Prelude hiding (Maybe(..))
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Prelude as P

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.Index.Points



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

data CheckNoCheck
  = Check
  | NoCheck
  deriving (Eq,Show)

data InnerOuter
  = Inner !CheckNoCheck !(Maybe Int)
  | Outer
  deriving (Eq,Show)

data ENE
  = EmptyT
  | NonEmptyT
  | ZeroT
  deriving (Eq,Show)



-- * Classes

-- |

class Elms x i where
  data Elm x i :: *
  type Arg x :: *
  getArg :: Elm x i -> Arg x
  getIdx :: Elm x i -> i

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

-- |

class (Monad m) => MkStream m x i where
  mkStream :: x -> InOut i -> i -> S.Stream m (Elm x i)

-- | Build the stack using (%)

class Build x where
  type Stack x :: *
  type Stack x = Z :!: x
  build :: x -> Stack x
  default build :: (Stack x ~ (Z :!: x)) => x -> Stack x
  build x = Z :!: x
  {-# INLINE build #-}

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

-- | 'outerCheck' acts as a static filter. If 'b' is true, we keep all stream
-- elements. If 'b' is false, we discard all stream elements.

outerCheck :: Monad m => Bool -> S.Stream m a -> S.Stream m a
outerCheck b (S.Stream step sS n) = b `seq` S.Stream snew (Left (b,sS)) Unknown where
  {-# INLINE [1] snew #-}
  snew (Left  (False,s)) = return $ S.Done
  snew (Left  (True ,s)) = return $ S.Skip (Right s)
  snew (Right s        ) = do r <- step s
                              case r of
                                S.Yield x s' -> return $ S.Yield x (Right s')
                                S.Skip    s' -> return $ S.Skip    (Right s')
                                S.Done       -> return $ S.Done
{-# INLINE outerCheck #-}



-- * Instances

-- |

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

instance EmptyENZ ENE where
  toEmptyENZ ene  | ene==NonEmptyT = EmptyT
                  | otherwise      = ene
  toNonEmptyENZ ene | ene==EmptyT  = NonEmptyT
                    | otherwise    = ene
  {-# INLINE toEmptyENZ #-}
  {-# INLINE toNonEmptyENZ #-}

-- | The bottom of every stack of RHS arguments in a grammar.

instance
  ( Monad m
  ) => MkStream m Z Subword where
  mkStream Z Outer !(Subword (i:.j)) = S.unfoldr step i where
    step !k
      | k==j      = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise = P.Nothing
  mkStream Z (Inner NoCheck Nothing)  !(Subword (i:.j)) = S.singleton $ ElmZ $ subword i i
  mkStream Z (Inner NoCheck (Just z)) !(Subword (i:.j)) = S.unfoldr step i where
    step !k
      | k<=j && k+z>=j = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise      = P.Nothing
  mkStream Z (Inner Check Nothing)   !(Subword (i:.j)) = S.unfoldr step i where
    step !k
      | k<=j      = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise = P.Nothing
  mkStream Z (Inner Check (Just z)) !(Subword (i:.j)) = S.unfoldr step i where
    step !k
      | k<=j && k+z>=j = P.Just $ (ElmZ (subword i i), j+1)
      | otherwise      = P.Nothing
  {-# INLINE mkStream #-}

instance ValidIndex Z Subword where
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}
  validIndex _ _ _ = True
  getParserRange _ _ = (0 :!: 0 :!: 0)

instance ValidIndex Z PointL where
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}
  validIndex _ _ _ = True
  getParserRange _ _ = (0 :!: 0 :!: 0)

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

instance (ValidIndex Z is, ValidIndex Z i) => ValidIndex Z (is:.i) where
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}
  validIndex _ _ _ = True
  getParserRange Z (is:.i) = getParserRange Z is :. getParserRange Z i

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

instance
  (
  ) => Elms Z ix where
  data Elm Z ix = ElmZ !ix
  type Arg Z = Z
  getArg !(ElmZ _) = Z
  getIdx !(ElmZ ix) = ix
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance Monad m => MkStream m Z Z where
  mkStream _ _ _ = S.singleton (ElmZ Z)
  {-# INLINE mkStream #-}

instance ValidIndex Z Z where
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}
  validIndex _ _ _ = True
  getParserRange _ _ = Z



-- * Special instances

instance Build x => Build (x:!:y) where
  type Stack (x:!:y) = Stack x :!: y
  build (x:!:y) = build x :!: y
  {-# INLINE build #-}

