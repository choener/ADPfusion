{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}

module ADP.Fusion.Examples.Palindrome where

import Data.Vector.Fusion.Stream.Monadic (Stream (..))
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector as V
import Data.Array.Repa.Index
import Control.Monad
import Control.Monad.Trans.Class
import qualified Control.Monad.Trans.Writer.Lazy as W
import qualified Control.Arrow as A

import Data.PrimitiveArray as PA
import Data.PrimitiveArray.Zero as PA

import ADP.Fusion.Point hiding (empty)




data SignatureT m x r = Signature
  { pair  :: Char -> x -> Char -> x
  , empty :: () -> x
  , h     :: Stream m x -> m r
  }

-- makeAlgebraProduct ''SignatureT

{-

-- gPalindrome :: Signature m x -> Empty -> Char -> tbl -> (tbl, Subword -> m x)

gPalindrome Signature{..} e c s =
  ( s, (  empty <<< e         |||
          pair  <<< c % s % c ... h
       )
  )
{-# INLINE gPalindrome #-}



aPair :: Monad m => Signature m Int Int
aPair = Signature
  { pair = \l x r -> if l==r then (x+4983) else -999999
  , empty = \() -> 4711
  , h = S.foldl' max (-888888)
  }
{-# INLINE aPair #-}

aPretty :: Monad m => Signature m String (Stream m String)
aPretty = Signature
  { pair = \l x r -> "(" ++ x ++ ")"
  , empty = \() -> ""
  , h = return . id
  }

(<**) :: (Monad m, CombElem x' x) => Signature m x x' -> Signature m y y' -> Signature m (x,Stream m y) y'
(<**) x y = Signature
  { pair = \l (zx,zy) r -> (pair x l zx r, S.map (\z -> pair y l z r) zy)
  , empty = \() -> (empty x (), S.singleton $ empty y ())
  , h = \zs -> do hfst <- h x $ S.map fst zs
                  h y $ S.concatMap snd . S.filter (combElem hfst . fst) $ zs
  }
{-# INLINE (<**) #-}

(***) :: (Monad m) => Signature m x x' -> Signature m y y' -> Signature m (x,y) (x',y')
(***) x y = Signature
  { pair = \l (zx,zy) r -> (pair x l zx r, pair y l zy r)
  , empty = \() -> (empty x (), empty y ())
--  , h = \zs -> do hfst <- h x $ S.map fst zs
--                  let phfs = S.concatMap snd . S.filter (combElem hfst . fst) $ zs
--                  hsnd <- h y phfs
  }
{-# INLINE (***) #-}

class CombElem x y where
  combElem :: x -> y -> Bool

instance (Eq x) => CombElem x x where
  combElem = (==)

instance (VU.Unbox x, Eq x) => CombElem (VU.Vector x) x where
  combElem xs y = VU.elem y xs

instance (Eq x) => CombElem (V.Vector x) x where
  combElem xs y = V.elem y xs

palindromeFill :: VU.Vector Char -> IO (PA.Unboxed (Z:.Subword) Int)
palindromeFill inp = do
  let n = VU.length inp
  !t' <- newWithM (Z:.subword 0 0) (Z:.subword 0 n) 0
  let t= mTblSw EmptyT t'
  let b = chr inp
  let e = Empty
  fillTable $ gPalindrome aPair e b t
  freeze t'
{-# NOINLINE palindromeFill #-}

fillTable (MTbl _ tbl, f) = do
  let (_,Z:.Subword (0:.n)) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    (f $ subword i j) >>= writeM tbl (Z:.subword i j)
{-# INLINE fillTable #-}

-}

