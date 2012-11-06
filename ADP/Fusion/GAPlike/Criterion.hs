{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PackageImports #-}

module ADP.Fusion.GAPlike.Criterion where

import Control.Monad.ST
import Criterion.Main
import Data.Char
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Fusion.Stream as SP

import Data.PrimitiveArray
import Data.PrimitiveArray.Unboxed.VectorZero as UVZ
import Data.PrimitiveArray.Unboxed.Zero as UZ
import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape

import ADP.Fusion.GAPlike
import ADP.Fusion.GAPlike.DevelCommon



criterionMain = defaultMain
  [ bgroup "testTTT3"
    [ bench "  10" (whnf (testTTT 0)   10)
    , bench " 100" (whnf (testTTT 0)  100)
    , bench "1000" (whnf (testTTT 0) 1000)
    ]
  , bgroup "testTTTT4"
    [ bench "  10" (whnf (testTTTT 0)   10)
    , bench " 100" (whnf (testTTTT 0)  100)
    , bench "1000" (whnf (testTTTT 0) 1000)
    ]
  , bgroup "testTTTT4ga"
    [ bench "  10" (whnf (testTTTTga 0)   10)
    , bench " 100" (whnf (testTTTTga 0)  100)
    , bench "1000" (whnf (testTTTTga 0) 1000)
    ]
  , bgroup "testTTTT4gaPA"
    [ bench "  10" (whnf (testTTTTgaPA 0)   10)
    , bench " 100" (whnf (testTTTTgaPA 0)  100)
    , bench "1000" (whnf (testTTTTgaPA 0) 1000)
    ]
  , bgroup "testTTTT4gaImmu"
    [ bench "  10" (whnf (testTTTTgaImmu 0)   10)
    , bench " 100" (whnf (testTTTTgaImmu 0)  100)
    , bench "1000" (whnf (testTTTTgaImmu 0) 1000)
    ]
  , bgroup "testTTTT4gaImmuPA"
    [ bench "  10" (whnf (testTTTTgaImmuPA 0)   10)
    , bench " 100" (whnf (testTTTTgaImmuPA 0)  100)
    , bench "1000" (whnf (testTTTTgaImmuPA 0) 1000)
    ]
  ]



-- * Criterion tests

testC :: Int -> Int -> Int
testC i j = runST doST where
  doST :: ST s Int
  doST = do
    let c = Chr dvu
    (gord1 <<< c ... ghsum) (i,j)
{-# NOINLINE testC #-}

gTestC (ord1,hsum) c =
  (ord1 <<< c ... hsum)

aTestC = (ord1,hsum) where
  ord1 = gord1
  hsum = ghsum

testCC :: Int -> Int -> Int
testCC i j = runST doST where
  doST :: ST s Int
  doST = do
    let c = Chr dvu
    let d = Chr dvu
    (gord2 <<< c % d ... ghsum) (i,j)
{-# NOINLINE testCC #-}

type TBL s = Tbl N (UVZ.MArr0 s DIM2 Int)

testT :: Int -> Int -> Int
testT i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl :: TBL s <- Tbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) 1 []
    (id <<< tbl ... ghsum) (i,j)
{-# NOINLINE testT #-}

testTT :: Int -> Int -> Int
testTT i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl :: TBL s <- Tbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) 1 []
    (gplus2 <<< tbl % tbl ... ghsum) (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testTT #-}

testTTT :: Int -> Int -> Int
testTTT i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl :: TBL s <- Tbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) 1 []
    (gplus3 <<< tbl % tbl % tbl ... ghsum) (i,j)
{-# NOINLINE testTTT #-}

testTTTT :: Int -> Int -> Int
testTTTT i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl :: TBL s <- Tbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) (1::Int) []
    (gplus4 <<< tbl % tbl % tbl % tbl ... ghsum) (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testTTTT #-}

testTTTTga :: Int -> Int -> Int
testTTTTga i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl :: TBL s <- Tbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) (1::Int) []
    gTTTga aTTTga tbl (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testTTTTga #-}

testTTTTgaPA :: Int -> Int -> Int
testTTTTgaPA i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl :: Tbl N (UZ.MArr0 s DIM2 Int) <- Tbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) (1::Int) []
    gTTTga aTTTga tbl (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testTTTTgaPA #-}

testTTTTgaImmu :: Int -> Int -> Int
testTTTTgaImmu i j =
    let tbl = (Tbl $ fromAssocs (Z:.0:.0) (Z:.j:.j) 1 []) :: Tbl N (UVZ.Arr0 DIM2 Int) 
    in tbl `seq` gTTTga aTTTgaImmu tbl (i,j)
{-# NOINLINE testTTTTgaImmu #-}

testTTTTgaImmuPA :: Int -> Int -> Int
testTTTTgaImmuPA i j =
    let tbl = (Tbl $ fromAssocs (Z:.0:.0) (Z:.j:.j) 1 []) :: Tbl N (UZ.Arr0 DIM2 Int) 
    in tbl `seq` gTTTga aTTTgaImmu tbl (i,j)
{-# NOINLINE testTTTTgaImmuPA #-}

gTTTga (plus4, hsum) tbl =
  (plus4 <<< tbl % tbl % tbl % tbl ... hsum)
{-# INLINE gTTTga #-}

aTTTga = (plus4, hsum) where
  plus4 = gplus4
  hsum = ghsum

aTTTgaImmu = (plus4, hsum) where
  plus4 = gplus4
  hsum = gihsum
{-# INLINE aTTTgaImmu #-}

gord1 a = ord a

gord2 a b = ord a + ord b

gord3 a b c = ord a + ord b + ord c

gplus2 a b = a+b

gplus3 a b c = a+b+c

gplus4 a b c d = a+b+c+d

ghsum :: S.Stream (ST s) Int -> ST s Int
ghsum = S.foldl' (+) 0

gihsum :: SP.Stream Int -> Int
gihsum = SP.foldl' (+) 0
