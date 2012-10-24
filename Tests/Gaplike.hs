{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | A mini-example showing how to use the new GAPlike-version of ADP together
-- with algebra products.
--
-- TODO if we use the NoMono, do we happen to be in the forall m case where
-- optimization doesn't happen?

module Tests.Gaplike where

import Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import Prelude as P
import "PrimitiveArray" Data.Array.Repa.Index
import Control.Monad.ST
import Data.Primitive
import Control.Monad.Primitive
import Control.Monad
import Data.Vector.Fusion.Util

import Data.PrimitiveArray as PA
import Data.PrimitiveArray.Unboxed.Zero as PA

import ADP.Fusion.GAPlike2

import Debug.Trace



-- | signature

type Signature m x =
  ( () -> x
  , Char -> x -> Char -> x
  , SM.Stream m x -> m x
  )

-- | Very simple grammar.

gSimple (empty,pair,h) tbl c e = 
  (tbl, empty <<< e           |||
        pair  <<< c % tbl % c ... h)
{-# INLINE gSimple #-}

-- | Simple scoring system

aMax :: Monad m => Signature m Int
aMax = (empty,pair,h) where
  empty _ = 0
  pair l x r = if l==r then x+1 else x
  h = SM.foldl' max (-999999)

-- | Pretty Printer

aPretty = (empty,pair,h) where
  empty _ = ""
  pair l x r = if l==r then "<" P.++ x P.++ ">" else "." P.++ x P.++ "."
  h = id

-- fill up

runFill inp = (arr ! (Z:.0:.n), bt) where
  (_,Z:._:.n) = bounds arr
  len = P.length inp
  arr = runST (fill vinp)
  vinp = VU.fromList $ inp
  bt = backtrack vinp arr

type TBL s = Tbl E (PA.MArr0 s DIM2 Int)

fill :: forall s . VU.Vector Char -> ST s (Arr0 DIM2 Int)
fill inp = do
  let n = VU.length inp
  t' <- fromAssocsM (Z:.0:.0) (Z:.n:.n) (-999999) []
  let t = Tbl t' -- :: TBL s
  let c = Chr inp
  let e = Empty
  fillTable $ gSimple aMax t c e
  PA.freeze t'

fillTable :: PrimMonad m => (Tbl E (MArr0 (PrimState m) DIM2 Int), ((Int,Int) -> m Int)) -> m ()
fillTable  (Tbl tbl, f) = do
  let (_,Z:.n:._) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    v <- f (i,j)
    v `seq` writeM tbl (Z:.i:.j) v

backtrack (inp :: VU.Vector Char) (tbl :: PA.Arr0 DIM2 Int) = unId . SM.toList $ g (0,n) where
  n = VU.length inp
  c = Chr inp
  e = Empty
  t = BTtbl tbl g
  (_,g) = gSimple ((aMax :: Signature Id Int) `aP` (aMax :: Signature Id Int)) t c e

bla (t :: (Int,Int) -> SM.Stream Id Int)
  = gSimple ((aMax :: Signature Id Int) `aP` (aMax :: Signature Id Int)) (BTtbl (undefined :: PA.Arr0 DIM2 Int) t) (Chr (undefined :: VU.Vector Char)) Empty

data BTtbl t g = BTtbl t g

instance Build (BTtbl t g) where
  type BuildStack (BTtbl t g) = None:.BTtbl t g
  build tbl = None:.tbl

type SI = SM.Stream Id Int
type ISI = SM.Stream Id (Int, SI)
type PISI = (Int,Int) -> ISI
type PSI = (Int,Int) -> SI

instance (StreamElement x) => StreamElement (x:.BTtbl (PA.Arr0 DIM2 Int) PSI) where
  data StreamElm    (x:.BTtbl (PA.Arr0 DIM2 Int) PSI) = SeBTtbl !(StreamElm x) !Int !Int SI
  type StreamTopIdx (x:.BTtbl (PA.Arr0 DIM2 Int) PSI) = Int
  type StreamArg    (x:.BTtbl (PA.Arr0 DIM2 Int) PSI) = StreamArg x :. (Int,SI)
  getTopIdx (SeBTtbl _ k _ _) = k
  getArg    (SeBTtbl x _ e g) = getArg x :. (e,g)

instance (Monad m, MkStream m x, StreamElement x, StreamTopIdx x ~ Int) => MkStream m (x:.BTtbl (PA.Arr0 DIM2 Int) PSI) where
  mkStream (x:.BTtbl t g) (i,j) = SM.map step $ mkStreamInner x (i,j) where
    step :: StreamElm x -> StreamElm (x:.BTtbl (PA.Arr0 DIM2 Int) PSI)
    step x = let k = getTopIdx x in SeBTtbl x j (t PA.! (Z:.k:.j)) (g (k,j))

-- |
--
-- TODO generalize the 'hfs' part: we need a type class, or s.th. as we either
-- need (==) or elem depending on 'f'

type APSignature =
  ( () -> (Int, SM.Stream Id Int)
  , Char -> (Int, SM.Stream Id Int) -> Char -> (Int, SM.Stream Id Int)
  , SM.Stream Id (Int, SM.Stream Id Int) -> SM.Stream Id Int
  )

instance Show (SM.Stream Id Int) where
  show xs = show $ unId $ SM.toList xs

aP
  :: Signature Id Int
  -> Signature Id Int
  -> APSignature
aP f s = (empty,pair,h) where
  (emptyF,pairF,hF) = f
  (emptyS,pairS,hS) = s

  empty :: () -> (Int, SM.Stream Id Int)
  empty e = let x = (emptyF e, SM.singleton (emptyS e)) in x

  pair :: Char -> (Int, SM.Stream Id Int) -> Char -> (Int, SM.Stream Id Int)
  pair l (x,ys) r = (pairF l x r,  SM.map (\y -> pairS l y r) ys)

  h :: SM.Stream Id (Int, SM.Stream Id Int) -> SM.Stream Id Int
  h xs = ss where -- traceShow (unId $ SM.toList ss) $ ss where
    hfs = unId . hF $ SM.map fst xs
    phfs = SM.filter ((hfs==) . fst) xs
    ss = SM.concatMap snd $ phfs

