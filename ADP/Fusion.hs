{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

-- | Generalized fusion system for grammars.
--
-- NOTE Symbols typically do not check bound data for consistency. If you, say,
-- bind a terminal symbol to an input of length 0 and then run your grammar,
-- you probably get errors, garbled data or random crashes. Such checks are
-- done via asserts in non-production code.

module ADP.Fusion where

import Control.DeepSeq
import Data.Array.Repa.Index
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Fusion.Stream as Sp
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Data.Vector.Fusion.Stream.Size

import Data.Array.Repa.Index.Subword
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import qualified Data.Array.Repa as R

import ADP.Fusion.Apply

import Debug.Trace

data InnerOuter
  = Inner
  | Outer
  deriving (Eq,Show)

infixl 3 :!:
data a :!: b = !a :!: !b

class Elms x i where
  data Elm x i :: *
  type Arg x :: *
  getArg :: Elm x i -> Arg x
  getIdx :: Elm x i -> i

class Index i where
  type InOut i :: *

instance Index (Int:!:Int) where
  type InOut (Int:!:Int) = InnerOuter

class (Monad m) => MkStream m x i where
  mkStream :: x -> InOut i -> i -> S.Stream m (Elm x i)

data Chr x = Chr !(VU.Vector x)

instance
  ( Elms ls (Int:!:Int)
  ) => Elms (ls :!: Chr x) (Int :!: Int) where
  data Elm (ls :!: Chr x) (Int :!: Int) = ElmChr !(Elm ls (Int :!: Int)) !x !(Int:!:Int)
  type Arg (ls :!: Chr x) = Arg ls :. x
  getArg !(ElmChr ls x _) = getArg ls :. x
  getIdx !(ElmChr _ _ idx) = idx
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

-- |
--
-- For 'Outer' cases, we extract the data, 'seq' it and then stream. This moves
-- extraction out of the loop.

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls (Int:!:Int)
  , MkStream m ls (Int :!: Int)
  ) => MkStream m (ls :!: Chr x) (Int :!: Int) where
  mkStream !(ls :!: Chr xs) Outer !(i :!: j) = let dta = VU.unsafeIndex xs (j-1) in dta `seq` S.map (\s -> ElmChr s dta (j-1 :!: j)) $ mkStream ls Outer (i :!: j-1)
--  mkStream !(ls :!: Chr xs) Outer !(i :!: j) = S.map (\s -> ElmChr s (VU.unsafeIndex xs (j-1)) (j-1 :!: j)) $ mkStream ls Outer (i :!: j-1)
  mkStream !(ls :!: Chr xs) Inner !(i :!: j) = S.map (\s -> let (k:!:l) = getIdx s in ElmChr s (VU.unsafeIndex xs l) (l:!:j)) $ mkStream ls Inner (i :!: j-1)
  {-# INLINE mkStream #-}

instance
  (
  ) => Elms Z (Int:!:Int) where
  data Elm Z (Int:!:Int) = ElmZ !(Int:!:Int)
  type Arg Z = Z
  getArg !(ElmZ _) = Z
  getIdx !(ElmZ ij) = ij
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  ) => MkStream m Z (Int:!:Int) where
  mkStream Z Outer (i:!:j) = S.unfoldr step i where
    step k
      | k==j      = Just $ (ElmZ (i:!:i), j+1)
      | otherwise = Nothing
  mkStream Z Inner (i:!:j) = S.unfoldr step i where
    step k
      | k<=j      = Just $ (ElmZ (i:!:i), j+1)
      | otherwise = Nothing
  {-# INLINE mkStream #-}

data Tbl x = Tbl !(R.Array R.U DIM2 x)

instance
  ( Elms ls (Int:!:Int)
  ) => Elms (ls :!: Tbl x) (Int:!:Int) where
  data Elm (ls :!: Tbl x) (Int:!:Int) = ElmTbl !(Elm ls (Int:!:Int)) !x !(Int:!:Int)
  type Arg (ls :!: Tbl x) = Arg ls :. x
  getArg !(ElmTbl ls x _) = getArg ls :. x
  getIdx !(ElmTbl _ _ idx) = idx
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls (Int:!:Int)
  , MkStream m ls (Int:!:Int)
  ) => MkStream m (ls:!:Tbl x) (Int:!:Int) where
  mkStream (ls:!:Tbl xs) Outer (i:!:j) = S.map (\s -> let (k:!:l) = getIdx s in ElmTbl s (R.unsafeIndex xs (R.ix2 i j)) (l:!:j)) $ mkStream ls Inner (i:!:j)
  mkStream (ls:!:Tbl xs) Inner (i:!:j) = S.flatten mk step Unknown $ mkStream ls Inner (i:!:j) where
    mk !s = let (k:!:l) = getIdx s in return (s :!: l)
    step !(s :!: k)
      | k > j = return S.Done
      | otherwise = return $ S.Yield (ElmTbl s (R.unsafeIndex xs (R.ix2 k j)) (k:!:j)) (s :!: k+1)
  {-# INLINE mkStream #-}

testF :: Int -> Int -> Int
testF i j = Sp.foldl' (+) 0 $ S.map (apply (p7) . getArg) $ mkStream (Z :!: Chr testVs :!: Chr testVs :!: Tbl testA :!: Tbl testA :!: Tbl testA :!: Chr testVs :!: Chr testVs) Outer (i:!:j)
{-# NOINLINE testF #-}

testA :: R.Array R.U DIM2 Int
testA = R.fromUnboxed (R.ix2 100 100) testVs
{-# NOINLINE testA #-}

testVs :: VU.Vector Int
testVs = VU.fromList [ 0 .. 9999 ]
{-# NOINLINE testVs #-}

p3 a b c = a+b+c
p4 a b c d = a+b+c+d
p5 a b c d e = a+b+c+d+e
p6 a b c d e f = a+b+c+d+e+f
p7 a b c d e f g = a+b+c+d+e+f+g

-- multi-tape version

data Term ts = Term !ts

data T = T

instance
  ( Monad m
  , MkStream m ls i
  , TermStream m ls i ts i
  ) => MkStream m (ls:!:Term ts) i where

class TermElms ts i where
  data TermElm x i :: *

class
  ( Monad m
  ) => TermStream m ls i ts j where
  termStream :: InOut j -> j -> S.Stream m (Elm ls i) -> S.Stream m (Elm ls i :!: TermElm ts j)

instance Index Z where
  type InOut Z = Z

instance Index (is :. (Int:!:Int)) where
  type InOut (is :. (Int:!:Int)) = InOut is :. InnerOuter

instance
  ( Monad m
  ) => TermStream m ls i T Z where

instance
  ( Monad m
  ) => TermStream m ls i (ts:.Chr c) (is :. (Int:!:Int)) where
  termStream (io:.Outer) (js:.(i:!:j)) xs = undefined

-- type level reverse

class Rev l r where
  type R l r :: *
  rev :: l -> r -> R l r

instance Rev Z r where
  type R Z r = r
  rev Z r = r

instance (Rev ts (rs:.h)) => Rev (ts:.h) rs where
  type R (ts:.h) rs = R ts (rs:.h)
  rev (ts:.h) rs = rev ts (rs:.h)


-- -- | Apply a function to symbols on the RHS of a production rule. Builds the
-- -- stack of symbols from 'xs' using 'build', then hands this stack to
-- -- 'mkStream' together with the initial 'iniT' telling 'mkStream' that we are
-- -- in the "outer" position. Once the stream has been created, we 'S.map'
-- -- 'getArg' to get just the arguments in the stack, and finally 'apply' the
-- -- function 'f'.
-- 
-- infixl 8 <<<
-- (<<<) f xs = S.map (apply f . getArg) . mkStream (build xs) initT
-- {-# INLINE (<<<) #-}
-- 
-- -- | Combine two RHSs to give a choice between parses.
-- 
-- infixl 7 |||
-- (|||) xs ys = \ij -> xs ij S.++ ys ij
-- {-# INLINE (|||) #-}
-- 
-- -- | Applies the objective function 'h' to a stream 's'. The objective function
-- -- reduces the stream to a single optimal value (or some vector of co-optimal
-- -- things).
-- 
-- infixl 6 ...
-- (...) s h = h . s
-- {-# INLINE (...) #-}
-- 
-- -- | Separator between RHS symbols.
-- 
-- infixl 9 ~~
-- (~~) = (:.)
-- {-# INLINE (~~) #-}
-- 
-- -- | This separator looks much paper "on paper" and is not widely used otherwise.
-- 
-- infixl 9 %
-- (%) = (:.)
-- {-# INLINE (%) #-}
-- 
-- 
-- instance NFData Z
-- instance NFData z => NFData (z:.VU.Vector e) where
--   rnf (z:.ve) = rnf z `seq` rnf ve
-- 
-- instance NFData z => NFData (z:.Int) where
--   rnf (z:.i) = rnf z `seq` rnf i
-- 
