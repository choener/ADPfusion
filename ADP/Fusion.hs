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

import Data.Array.Repa.Index.Subword

import ADP.Fusion.Apply
import ADP.Fusion.Chr
import ADP.Fusion.Classes
import ADP.Fusion.None
import ADP.Fusion.Region
--import ADP.Fusion.Table
--import ADP.Fusion.Term

import Debug.Trace

{-

infixl 8 <<<
(<<<) :: (Monad m, MkElm x i, Apply (Arg x -> r))
      => Fun (Arg x -> r)
      -> S.Stream m (Elm x i)
      -> S.Stream m (Elm x i :. r)
(<<<) f xs = S.map (\x -> (x :. (apply f $ getArg x))) xs
{-# INLINE (<<<) #-}

infixl 7 |||
(|||) xs ys ij = xs ij S.++ ys ij
{-# INLINE (|||) #-}

infixl 6 ...
(...) s h ij = h $ s ij
{-# INLINE (...) #-}

-}

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
--  x <- return 1
--  x <- S.length $ mkS None (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region ys)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs:.Region xs) :. Term (T:.Region xs:.Region xs)) (IsTii (IsTii (IsTz Z:. Outer) :. Outer)) (Z:.(i:.j):.(i:.j))
--  a <- S.foldl' (+) 0 $ S.map (apply VU.unsafeLast . getArg) $ mkStream (None :. Region xs) (IxTsubword Outer) (Subword (i:.j))
--  a `seq` print a
--  b <- S.foldl' (+) 0 $ S.map (apply p2 . getArg) $ mkStream (None :. Region xs :. Region xs) (IxTsubword Outer) (Subword (i:.j))
--  b `seq` print b
--  c <- S.foldl' (+) 0 $ S.map (\x -> x `deepseq` (apply p3 . getArg $ x)) $ mkStream (None :. Region xs :. Region ys :. Region zs) (IxTsubword Outer) (Subword (i:.j))
--  c `seq` print (j,c)
--  d <- S.foldl' (+) 0 $ S.map (apply p4 . getArg) $ mkStream (None :. Region xs :. Region xs :. Region xs :. Region xs) (IxTsubword Outer) (Subword (i:.j))
--  d `seq` print (j,d)
--  e <- S.foldl' (+) 0 $ S.map (apply fc . getArg) $ mkStream (None :. Chr xs) (IxTsubword Outer) (Subword (i:.j))
--  e `seq` print (j,e)
  e <- S.foldl' (+) 0 $ S.map (apply fcrrc . getArg) $ mkStream (None :. Chr xs :. Region ys :. Region zs :. Chr xs) (IxTsubword Outer) (Subword (i:.j))
  e `seq` print (j,e)
  return 0
{-# NOINLINE testInner #-}

instance NFData Z
instance NFData z => NFData (z:.VU.Vector e) where
  rnf (z:.ve) = rnf z `seq` rnf ve

instance NFData z => NFData (z:.Int) where
  rnf (z:.i) = rnf z `seq` rnf i

fcrrc a b c d = a + VU.unsafeLast b + VU.unsafeHead c + d

fc a = a

p2 a b = (a,b) `deepseq` (VU.unsafeLast a + VU.unsafeHead b)
{-# INLINE p2 #-}

p3 a b c = (a,b,c) `deepseq` (VU.unsafeLast a + VU.unsafeLast b + VU.unsafeHead c)
{-# INLINE p3 #-}

p4 a b c d = (a,b,c,d) `deepseq` (VU.unsafeLast a + VU.unsafeLast b + VU.unsafeLast c + VU.unsafeHead d)
{-# INLINE p4 #-}

