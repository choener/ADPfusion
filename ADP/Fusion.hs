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
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM

import Data.Array.Repa.Index.Subword
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import ADP.Fusion.Apply
import ADP.Fusion.Chr
import ADP.Fusion.Classes
import ADP.Fusion.Region
import ADP.Fusion.Table
--import ADP.Fusion.Term

import Debug.Trace



-- | Apply a function to symbols on the RHS of a production rule. Builds the
-- stack of symbols from 'xs' using 'build', then hands this stack to
-- 'mkStream' together with the initial 'iniT' telling 'mkStream' that we are
-- in the "outer" position. Once the stream has been created, we 'S.map'
-- 'getArg' to get just the arguments in the stack, and finally 'apply' the
-- function 'f'.

infixl 8 <<<
(<<<) f xs = S.map (apply f . getArg) . mkStreamO (build xs) initT
{-# INLINE (<<<) #-}

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
(~~) = (:.)
{-# INLINE (~~) #-}

-- | This separator looks much paper "on paper" and is not widely used otherwise.

infixl 9 %
(%) = (:.)
{-# INLINE (%) #-}

{-

-- * testing

test :: Int -> IO Int
test k =
  let
    xs = VU.enumFromN (0::Int) (2 * k)
    ys = VU.enumFromN (0::Int) (2 * k)
    zs = VU.enumFromN (0::Int) (2 * k)
    i = 0 :: Int
    j = k :: Int
  in do
    (xs,ys,zs,i,j) `deepseq` testInner k xs ys zs i j
{-# NOINLINE test #-}

testInner :: Int -> VU.Vector Int -> VU.Vector Int -> VU.Vector Int -> Int -> Int -> IO Int
testInner !k !xs !ys !zs !i !j = do
  (!mxs) :: (PA.MU IO (Z:.Subword) Int) <- PA.newWithM (Z:. Subword (0:.0)) (Z:. Subword (0:.k)) (1 :: Int)
  (!mys) :: (PA.MU IO (Z:.Subword) Int) <- PA.newWithM (Z:. Subword (0:.0)) (Z:. Subword (0:.k)) (2 :: Int)
  (!mzs) :: (PA.MU IO (Z:.Subword) Int) <- PA.newWithM (Z:. Subword (0:.0)) (Z:. Subword (0:.k)) (3 :: Int)
  let region xs = Region Nothing Nothing xs
      {-# INLINE region #-}
  let mtable xs = MTable Tmany xs
--  mapM_ (\(i,j,x) -> x >>= \x' -> print (i,j,x')) $ [ (i,j,PA.readM mxs (Z:.Subword (i:.j))) | i <- [0..k], j <- [i..k]]
--  x <- return 1
--  x <- S.length $ mkS None (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region ys)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs:.Region xs) :. Term (T:.Region xs:.Region xs)) (IsTii (IsTii (IsTz Z:. Outer) :. Outer)) (Z:.(i:.j):.(i:.j))
--  a <- S.foldl' (+) 0 $ S.map (apply VU.unsafeLast . getArg) $ mkStream (None :. region xs) (IxTsubword Outer) (Subword (i:.j))
--  a `seq` print a
--  c <- S.foldl' (+) 0 $ S.map (\x -> x `deepseq` (apply p3 . getArg $ x)) $ mkStream (None :. region xs :. region ys :. region zs) (IxTsubword Outer) (Subword (i:.j))
--  c `seq` print (j,c)
--  d <- S.foldl' (+) 0 $ S.map (apply p4 . getArg) $ mkStream (None :. Region xs :. Region xs :. Region xs :. Region xs) (IxTsubword Outer) (Subword (i:.j))
--  d `seq` print (j,d)
--  e <- S.foldl' (+) 0 $ S.map (apply fc . getArg) $ mkStream (None :. Chr xs) (IxTsubword Outer) (Subword (i:.j))
--  e `seq` print (j,e)
--  e <- S.foldl' (+) 0 $ S.map (apply fcrrc . getArg) $ mkStream (None :. Chr xs :. Region ys :. Region zs :. Chr xs) (IxTsubword Outer) (Subword (i:.j))
--  e `seq` print (j,e)
--  f <- S.foldl' (+) 0 $ S.map (apply (\a b c d -> a+b+c+d) . getArg) $ mkStream (None :. mtable mxs :. mtable mys :. mtable mzs :. mtable mxs) (IxTsubword Outer) (Subword (i:.j))
--  f `seq` print (j,f)
-- NEW NEW NEW
--  a <- VU.unsafeLast <<< region xs ... S.foldl' (+) 0 $ subword i j
--  a `seq` print a
--  b <- p2 <<< region xs % region ys ... S.foldl' (+) 0 $ subword i j
--  b `seq` print b
  f <- (\a b c d -> a+b+c+d) <<< mtable mxs % mtable mys % mtable mzs % mtable mxs ... S.foldl' (+) 0 $ subword i j
  f `seq` print (j,f)
  return 0
{-# NOINLINE testInner #-}

-}

instance NFData Z
instance NFData z => NFData (z:.VU.Vector e) where
  rnf (z:.ve) = rnf z `seq` rnf ve

instance NFData z => NFData (z:.Int) where
  rnf (z:.i) = rnf z `seq` rnf i

{-

fcrrc a b c d = a + VU.unsafeLast b + VU.unsafeHead c + d

fc a = a

p2 a b = (a,b) `deepseq` (VU.unsafeLast a + VU.unsafeHead b)
{-# INLINE p2 #-}

p3 a b c = (a,b,c) `deepseq` (VU.unsafeLast a + VU.unsafeLast b + VU.unsafeHead c)
{-# INLINE p3 #-}

p4 a b c d = (a,b,c,d) `deepseq` (VU.unsafeLast a + VU.unsafeLast b + VU.unsafeLast c + VU.unsafeHead d)
{-# INLINE p4 #-}

-}

