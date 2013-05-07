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



-- | The Inner/Outer handler. We encode three states. We are in 'Outer' or
-- right-most position, or 'Inner' position. The 'Inner' position encodes if
-- loop conditional 'CNC' need to be performed.
--
-- In f <<< Z % table % table, the two tables already perform a conditional
-- branch, so that Z/table does not have to check boundary conditions.
--
-- In f <<< Z % table % char, no check is performed in table/char, so Z/table
-- needs to perform a boundary check.

data CNC
  = Check
  | NoCheck
  deriving (Eq,Show)

data InnerOuter
  = Inner !CNC !(Maybe Int)
  | Outer
  deriving (Eq,Show)

data ENE
  = EmptyT
  | NoEmptyT
  deriving (Eq,Show)

class TransENE t where
  toEmpty :: t -> t
  toNonEmpty :: t -> t

class Elms x i where
  data Elm x i :: *
  type Arg x :: *
  getArg :: Elm x i -> Arg x
  getIdx :: Elm x i -> i

class Index i where
  type InOut i :: *

instance Index Subword where
  type InOut Subword = InnerOuter

instance Index (is:.i) where
  type InOut (is:.i) = InOut is :. InnerOuter

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

instance Build x => Build (x:!:y) where
  type Stack (x:!:y) = Stack x :!: y
  build (x:!:y) = build x :!: y
  {-# INLINE build #-}

instance
  (
  ) => Elms Z Subword where
  data Elm Z Subword = ElmZ !Subword
  type Arg Z = Z
  getArg !(ElmZ _) = Z
  getIdx !(ElmZ ij) = ij
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

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

-- Calculate the static extends of a RHS. With a bit of trickery, we can even
-- check that left-/righ-linear grammars are always legal.

class StaticStack x i where
  -- | Statically calculate how many steps we have to be away from "0" (fst),
  -- the minimal size of the subword for this rule (snd), and how many steps we
  -- have to be away from the whole input size "N".
  staticStack :: x -> (Int :!: i :!: Int)
  -- | Returns the maximal input size of a stack element. Stacks should
  -- scrutinize "earlier" Maybe's to make sure everything checks out, say, all
  -- extends are the same.
  --
  -- TODO this could become weird if multiple input strings are joined in the
  -- same RHS. Does this even happen? Applications?
  staticExtends :: x -> Maybe i

-- | 'Z' requires only an empty subword and has no extends.

instance StaticStack Z Subword where
  staticStack Z = (0 :!: subword 0 0 :!: 0)
  staticExtends Z = Nothing
  {-# INLINE staticStack #-}

class StaticCheck i where
  staticCheck :: StaticStack x i => x -> i -> Bool

instance StaticCheck Subword where
  staticCheck stack (Subword(i:.j))
    | Nothing <- se               = error "StaticCheck:staticCheck: illegal stack!"
    | Just (Subword (z:.n)) <- se = z+a<=i && j+b<=n && k+l<=j-i
    where
      (a :!: Subword (k:.l) :!: b) = staticStack stack
      !se = staticExtends stack
  {-# INLINE staticCheck #-}

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

