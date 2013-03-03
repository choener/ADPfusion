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

--import ADP.Fusion.Apply
--import ADP.Fusion.Chr
import ADP.Fusion.Classes
import ADP.Fusion.None
import ADP.Fusion.Region
--import ADP.Fusion.Table
--import ADP.Fusion.Term


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
    xs = VU.enumFromN (0::Int) (2 * k) -- fromList [0 .. 9999 :: Int]
--    ys = VU.empty  -- VU.fromList [ 0 .. 999 :: Int] -- VU.reverse xs
    i = 0 :: Int
    j = k :: Int
  in do
    (xs,i,j) `deepseq` testInner k xs xs i j
{-# NOINLINE test #-}

testInner :: Int -> VU.Vector Int -> VU.Vector Int -> Int -> Int -> IO Int
testInner !k !xs !ys !i !j = do
--  x <- return 1
--  x <- S.length $ mkS None (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region ys)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs) :. Term (T:.Region xs)) (IsTii (IsTz Z :. Outer)) (Z:.(i:.j))
--  x <- S.length $ mkS (None :. Term (T:.Region xs:.Region xs) :. Term (T:.Region xs:.Region xs)) (IsTii (IsTii (IsTz Z:. Outer) :. Outer)) (Z:.(i:.j):.(i:.j))
--  a <- S.length $ mkStream (None :. Region xs) (IxTsubword Outer) (Subword (i:.j))
--  a `seq` print a
--  b <- S.length $ mkStream (None :. Region xs :. Region xs) (IxTsubword Outer) (Subword (i:.j))
--  b `seq` print b
  c <- S.length $ mkStream (None :. Region xs :. Region xs :. Region xs :. Region xs) (IxTsubword Outer) (Subword (i:.j))
  c `seq` print (j,c)
  return 0
{-# NOINLINE testInner #-}

