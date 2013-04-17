{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RankNTypes #-}
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
--
-- TODO each combinator should come with a special outer check. Given some
-- index (say (i,j), this can then check if i-const >= 0, or j+const<=n, or
-- i+const<=j. That should speed up everything that uses GChr combinators.
-- Separating out this check means that certain inner loops can run without any
-- conditions and just jump.

module ADP.Fusion where

import Control.DeepSeq
import Control.Monad.Primitive
import Data.Array.Repa.Index
import Data.Strict.Maybe
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Size
import GHC.Exts (inline)
import Prelude hiding (Maybe(..))
import qualified Data.Vector.Fusion.Stream as Sp
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import qualified Prelude as P

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.ExtShape
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import qualified Data.Array.Repa as R

import ADP.Fusion.Apply
import ADP.Fusion.Chr
import ADP.Fusion.Classes
import ADP.Fusion.Empty
import ADP.Fusion.Region
import ADP.Fusion.Table

import Debug.Trace








{-
testF :: Int -> Int -> Int
testF i j =
  p7' <<< chrR testVs % chrL testVs % Tbl testA % region testVs % Tbl testA % chrR testVs % chrL testVs |||
  p7' <<< chrR testVs % chrL testVs % Tbl testA % region testVs % Tbl testA % chrR testVs % chrL testVs ... (Sp.foldl' (+) 0) $ subword i j
{-# NOINLINE testF #-}
-}

testG :: Int -> Int -> Int
testG i j =
  p7 <<< chr testVs % chr testVs % Tbl testA % Tbl testA % Tbl testA % chr testVs % chr testVs |||
  p7 <<< chr testVs % chr testVs % Tbl testA % Tbl testA % Tbl testA % chr testVs % chr testVs ... (Sp.foldl' (+) 0) $ subword i j
{-# NOINLINE testG #-}

testA :: PA.Unboxed (Z:.Subword) Int
testA = PA.fromAssocs (Z:.subword 0 0) (Z:.subword 0 50) 0 []
{-# NOINLINE testA #-}

testVs :: VU.Vector Int
testVs = VU.fromList [ 0 .. 9999 ]
{-# NOINLINE testVs #-}

{-
--gugg :: Int -> Int -> [(Int,VU.Vector Int,Int)]
gugg i j = (,,) <<< chrR testVs % region testVs % chrL testVs ... Sp.toList $ subword i j
-}

p3 a b c = a+b+c
p4 a b c d = a+b+c+d
p5 a b c d e = a+b+c+d+e
p6 a b c d e f = a+b+c+d+e+f
p7 a b c d e f g = a+b+c+d+e+f+g
p7' (a:!:a') (b:!:b') c ds e (f:!:f') (g:!:g') = a+b+c+ VU.length ds +e+f+g + a'+b'+f'+g'
p7'' (a:!:a') (b:!:b') c d e (f:!:f') (g:!:g') = a+b+c+ d +e+f+g + a'+b'+f'+g'




-- multi-tape version

{-
data Term ts = Term !ts

data T = T

class TermIdx ix where
  allOuter :: ix -> InOut ix -> Bool
  anyOuter :: ix -> InOut ix -> Bool

instance TermIdx Z where
  allOuter Z _ = True
  anyOuter Z _ = True
  {-# INLINE allOuter #-}
  {-# INLINE anyOuter #-}

instance (TermIdx is) => TermIdx (is:.i) where
  allOuter (is:._) (os:.o) = case o of
    Inner -> False
    Outer -> allOuter is os
  anyOuter (is:._) (os:.o) = case o of
    Outer -> True
    Inner -> anyOuter is os
  {-# INLINE allOuter #-}
  {-# INLINE anyOuter #-}

class TermElms ts ix where
  data TermElm ts ix :: *
--  data MaybeTermElm ts ix :: *
  preAllTerm :: ts -> ix -> TermElm ts ix
  preAnyTerm :: ts -> ix -> TermElm ts ix

class TermIoIdx ts ix where
  termIO :: ts -> InOut ix -> ix -> InOut ix
  termIX :: ts -> InOut ix -> ix -> ix

instance
  ( Monad m
  , TermIdx ix
  , TermElms ts ix
  , TermIoIdx ts ix
  , MkStream m ls ix
  ) => MkStream m (ls:!:Term ts) ix where
  mkStream (ls:!:Term ts) io ix
    | allOuter ix io = let pre = preAllTerm ts ix
                           f p = return undefined
                       in pre `seq` S.mapM (f pre) $ mkStream ls (termIO ts io ix) (termIX ts io ix)
    | anyOuter ix io = let pre = preAnyTerm ts ix
                           f p = return undefined
                           mk  = undefined
                           step = undefined
                       in pre `seq` S.mapM (f pre) $ S.flatten mk step Unknown $ mkStream ls (termIO ts io ix) (termIX ts io ix)
    | otherwise      = let mk = undefined
                           step = undefined
                       in S.flatten mk step Unknown $ mkStream ls (termIO ts io ix) (termIX ts io ix)
  {-# INLINE mkStream #-}

testMT :: Int -> Int -> Int
testMT i j = Sp.foldl' (+) 0
           $ S.map (apply mtp3 . getArg)
           $ mkStream (Z :!: Term (T:.Chr testVs:.Chr testVs) :!: Tbl4 testAA :!: Term (T:.Chr testVs:.Chr testVs))
                      (Z:.Outer:.Outer)
                      (Z:.(i:!:j):!:(i:!:j))

data Tbl4 x = Tbl4 !(R.Array R.U DIM4 x)

testAA :: R.Array R.U DIM4 Int
testAA = R.fromUnboxed (R.ix4 20 20 20 20) (VU.fromList [ 0 .. 20^4 ])
{-# NOINLINE testAA #-}

mtp3 (T:.a:.b) k (T:.c:.d) = a+b + k + c+d
-}

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


-- | Apply a function to symbols on the RHS of a production rule. Builds the
-- stack of symbols from 'xs' using 'build', then hands this stack to
-- 'mkStream' together with the initial 'iniT' telling 'mkStream' that we are
-- in the "outer" position. Once the stream has been created, we 'S.map'
-- 'getArg' to get just the arguments in the stack, and finally 'apply' the
-- function 'f'.

infixl 8 <<<
(<<<) f xs = \ij -> outerCheck (staticCheck (build xs) ij) . S.map (apply (inline f) . getArg) . mkStream (build xs) Outer $ ij
{-# INLINE (<<<) #-}

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

-- | Combine two RHSs to give a choice between parses.

infixl 7 |||
(|||) xs ys = \ij -> xs ij S.++ ys ij
{-# INLINE (|||) #-}

-- | Applies the objective function 'h' to a stream 's'. The objective function
-- reduces the stream to a single optimal value (or some vector of co-optimal
-- things).

infixl 6 ...
(...) s h = h . s
{-# INLINE (...) #-}

-- | Separator between RHS symbols.

infixl 9 ~~
(~~) = (:!:)
{-# INLINE (~~) #-}

-- | This separator looks much paper "on paper" and is not widely used otherwise.

infixl 9 %
(%) = (:!:)
{-# INLINE (%) #-}

-- 
-- instance NFData Z
-- instance NFData z => NFData (z:.VU.Vector e) where
--   rnf (z:.ve) = rnf z `seq` rnf ve
-- 
-- instance NFData z => NFData (z:.Int) where
--   rnf (z:.i) = rnf z `seq` rnf i
-- 


