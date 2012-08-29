{-# LANGUAGE EmptyDataDecls #-}
{- LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

-- | 

module ADP.Fusion.GAPlike2 where

import Control.Monad.Primitive
import Control.Monad.ST
import Data.Primitive
import Data.PrimitiveArray
import Data.PrimitiveArray.Unboxed.Zero as UZ
import Data.PrimitiveArray.Unboxed.VectorZero as UVZ
import Data.Vector.Fusion.Stream.Size
import GHC.Prim (Constraint)
import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Fusion.Stream as SP
import qualified Data.Vector.Unboxed as VU
import Text.Printf
import Data.List (intersperse)
import Data.Char




class StreamElement x where
  -- | one element of the stream, recursively defined
  data StreamElm x :: *
  -- | top-most index of the stream -- typically int
  type StreamTopIdx  x :: *
  -- | complete, recursively defined argument of the stream
  type StreamArg  x :: *
  -- | Given a stream element, we extract the top-most idx
  getTopIdx :: StreamElm x -> StreamTopIdx x
  -- | extract the recursively defined argument in a well-defined way for 'apply'
  getArg :: StreamElm x -> StreamArg x

class (StreamConstraint x) => MkStream m x where
  type StreamConstraint x :: Constraint
  type StreamConstraint x = ()
  mkStream      :: (StreamConstraint x) => x -> (Int,Int) -> S.Stream m (StreamElm x)
  mkStreamInner :: (StreamConstraint x) => x -> (Int,Int) -> S.Stream m (StreamElm x)



-- * Default instances of StreamElement / MkStream

-- ** Terminates the stack of arguments

-- | Very simple data ctor

data None = None

-- | For CORE-language, we have our own Arg-terminator

data ArgZ = ArgZ

instance StreamElement None where
  data StreamElm None    = SeNone !Int
  type StreamTopIdx None = Int
  type StreamArg    None = ArgZ
  getTopIdx (SeNone k) = k
  getArg _ = ArgZ
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m) => MkStream m None where
  mkStream None (i,j) = S.unfoldr step i where
    step k
      | k<=j = Just (SeNone i, j+1)
      | otherwise = Nothing
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  mkStreamInner = mkStream
  {-# INLINE mkStreamInner #-}

-- ** A single character terminal. Using unboxed vector to hold the input.

data Chr e = Chr !(VU.Vector e)

instance Build (Chr e) where
  type BuildStack (Chr e) = None:.(Chr e)
  build c = None:.c
  {-# INLINE build #-}

instance (StreamElement x) => StreamElement (x:.Chr e) where
  data StreamElm (x:.Chr e) = SeChr !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Chr e) = Int
  type StreamArg (x:.Chr e) = StreamArg x :. e
  getTopIdx (SeChr _ k _) = k
  getArg (SeChr x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.Chr e) where
  mkStream (x:.Chr es) (i,j) = S.flatten mk step Unknown $ mkStream x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Chr e)))
    step (x,k)
      | k+1 == j = return $ S.Yield (SeChr x (k+1) (VU.unsafeIndex es k)) (x,j+1)
      | otherwise = return S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  mkStreamInner (x:.Chr es) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Chr e)))
    step (x,k)
      | k < j     = return $ S.Yield (SeChr x (k+1) (VU.unsafeIndex es k)) (x,j+1)
      | otherwise = return $ S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStreamInner #-}

-- ** Non-empty two-dimensional subwords, for non-terminal use

data NonEmptyTbl s e = NonEmptyTbl !(UVZ.MArr0 s DIM2 e)

instance Build (NonEmptyTbl s e) where
  type BuildStack (NonEmptyTbl s e) = None:.NonEmptyTbl s e
  build t = None:.t
  {-# INLINE build #-}

instance (StreamElement x) => StreamElement (x:.NonEmptyTbl s e) where
  data StreamElm (x:.NonEmptyTbl s e) = SeNonEmptyTbl !(StreamElm x) !Int !e
  type StreamTopIdx (x:.NonEmptyTbl s e) = Int
  type StreamArg (x:.NonEmptyTbl s e) = StreamArg x :. e
  getTopIdx (SeNonEmptyTbl _ k _) = k
  getArg (SeNonEmptyTbl x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.NonEmptyTbl s e) where
  {-
  mkStream (x:.NonEmptyTbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x,getTopIdx x)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.NonEmptyTbl s e)))
    step (x,k)
      | k < j = readM t (Z:.k:.j) >>= \e -> return $ S.Yield (SeNonEmptyTbl x k e) (x,j+1)
      | otherwise = return S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  -}
  mkStream (x:.NonEmptyTbl t) (i,j) = S.mapM step $ mkStreamInner x (i,j-1) where
    step :: StreamElm x -> m (StreamElm (x:.NonEmptyTbl s e))
    step x = let k = getTopIdx x in readM t (Z:.k:.j) >>= \e -> return $ SeNonEmptyTbl x k e
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  mkStreamInner (x:.NonEmptyTbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x,getTopIdx x + 1)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.NonEmptyTbl s e)))
    step (x,l)
      | k<l && l <= j = readM t (Z:.k:.l) >>= \e -> return $ S.Yield (SeNonEmptyTbl x l e) (x,l+1)
      | otherwise = return S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStreamInner #-}

-- ** Defaulting to non-empty for two-dimensional tables

instance Build (UVZ.MArr0 s DIM2 e) where
  type BuildStack (UVZ.MArr0 s DIM2 e) = None:.UVZ.MArr0 s DIM2 e
  build t = None:.t
  {-# INLINE build #-}

instance (StreamElement x) => StreamElement (x:.UVZ.MArr0 s DIM2 e) where
  data StreamElm (x:.UVZ.MArr0 s DIM2 e) = SeUVZMA !(StreamElm x) !Int !e
  type StreamTopIdx (x:.UVZ.MArr0 s DIM2 e) = Int
  type StreamArg (x:.UVZ.MArr0 s DIM2 e) = StreamArg x :. e
  getTopIdx (SeUVZMA _ k _) = k
  getArg (SeUVZMA x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.UVZ.MArr0 s DIM2 e) where
  mkStream (x:.t) (i,j) = S.mapM step $ mkStreamInner x (i,j-1) where
    step :: StreamElm x -> m (StreamElm (x:.UVZ.MArr0 s DIM2 e))
    step x = let k = getTopIdx x in readM t (Z:.k:.j) >>= \e -> return $ SeUVZMA x k e
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  mkStreamInner (x:.t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x,getTopIdx x + 1)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.UVZ.MArr0 s DIM2 e)))
    step (x,l)
      | k<l && l <= j = readM t (Z:.k:.l) >>= \e -> return $ S.Yield (SeUVZMA x l e) (x,l+1)
      | otherwise = return S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStreamInner #-}

-- ** by default, every table should be wrapped. Instances for wrapped two-dim.
-- tables with underlying primitive or unboxed-vector instances.

data E -- | empty subwords allowed

data N -- | only non-empty subwords

data Tbl c es = Tbl !es

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.Tbl E (UVZ.MArr0 s DIM2 e)) where

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.Tbl N (UVZ.MArr0 s DIM2 e)) where

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.Tbl E (UZ.MArr0 s DIM2 e)) where

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.Tbl N (UZ.MArr0 s DIM2 e)) where

instance (MkStream m (x:.Tbl N y)) => MkStream m (x:.Tbl N (Tbl E y)) where
--  mkStream (x:.Tbl (Tbl t)) = mkStream (x:.Tbl t)

-- * Build

class Build x where
  type BuildStack x :: *
  build :: x -> BuildStack x

instance Build x => Build (x,y) where
  type BuildStack (x,y) = BuildStack x :. y
  build (x,y) = build x :. y
  {-# INLINE build #-}



-- * combinators

infixl 8 <<<
(<<<) f t ij = S.map (\s -> apply f $ getArg s) $ mkStream (build t) ij
{-# INLINE (<<<) #-}

infixl 7 |||
(|||) xs ys ij = xs ij S.++ ys ij
{-# INLINE (|||) #-}

infixl 6 ...
(...) s h ij = h $ s ij
{-# INLINE (...) #-}

infixl 9 ~~
(~~) = (,)
{-# INLINE (~~) #-}

infixl 9 %
(%) = (,)
{-# INLINE (%) #-}










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

testT :: Int -> Int -> Int
testT i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl <- NonEmptyTbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) 1 []
    (id <<< tbl ... ghsum) (i,j)
{-# NOINLINE testT #-}

testTT :: Int -> Int -> Int
testTT i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl <- NonEmptyTbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) 1 []
    (gplus2 <<< tbl % tbl ... ghsum) (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testTT #-}

testTTT :: Int -> Int -> Int
testTTT i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl <- NonEmptyTbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) 1 []
    (gplus3 <<< tbl % tbl % tbl ... ghsum) (i,j)
{-# NOINLINE testTTT #-}

testTTTT :: Int -> Int -> Int
testTTTT i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl <- NonEmptyTbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) (1::Int) []
    (gplus4 <<< tbl % tbl % tbl % tbl ... ghsum) (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testTTTT #-}

testTTTTga :: Int -> Int -> Int
testTTTTga i j = runST doST where
  doST :: ST s Int
  doST = do
    tbl <- NonEmptyTbl `fmap` fromAssocsM (Z:.0:.0) (Z:.j:.j) (1::Int) []
    -- (gplus4 <<< tbl % tbl % tbl % tbl ... ghsum) (i,j)
    gTTTga aTTTga tbl (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testTTTTga #-}

gTTTga (plus4, hsum) tbl =
  (plus4 <<< tbl % tbl % tbl % tbl ... hsum)

aTTTga = (plus4, hsum) where
  plus4 = gplus4
  hsum = ghsum

gord1 a = ord a

gord2 a b = ord a + ord b

gord3 a b c = ord a + ord b + ord c

gplus2 a b = a+b

gplus3 a b c = a+b+c

gplus4 a b c d = a+b+c+d

ghsum :: S.Stream (ST s) Int -> ST s Int
ghsum = S.foldl' (+) 0

dvu = VU.fromList $ concat $ replicate 10 ['a'..'z']
{-# NOINLINE dvu #-}

{-
testM3 :: Int -> Int -> Int
testM3 i j = runST doST where
  doST :: ST s Int
  doST = do
    s :: UZ.MArr0 s DIM2 Int <- fromAssocsM (Z:.0:.0) (Z:.j:.j) 0 []
    S.length $ mkStream (ArgBottom:.s:.s:.s) (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testM3 #-}

testM4 :: Int -> Int -> Int
testM4 i j = runST doST where
  doST :: ST s Int
  doST = do
    s :: UZ.MArr0 s DIM2 Int <- fromAssocsM (Z:.0:.0) (Z:.j:.j) 0 []
    S.length $ mkStream (ArgBottom:.s:.s:.s:.s) (i,j)
  {-# INLINE doST #-}
{-# NOINLINE testM4 #-}
-}

class Apply x where
  type Fun x :: *
  apply :: Fun x -> x

instance Apply (ArgZ:.a -> res) where
  type Fun (ArgZ:.a -> res) = a -> res
  apply fun (ArgZ:.a) = fun a
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b -> res) where
  type Fun (ArgZ:.a:.b -> res) = a->b -> res
  apply fun (ArgZ:.a:.b) = fun a b
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c -> res) where
  type Fun (ArgZ:.a:.b:.c -> res) = a->b->c -> res
  apply fun (ArgZ:.a:.b:.c) = fun a b c
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d -> res) where
  type Fun (ArgZ:.a:.b:.c:.d -> res) = a->b->c->d -> res
  apply fun (ArgZ:.a:.b:.c:.d) = fun a b c d
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e -> res) = a->b->c->d->e -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e) = fun a b c d e
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f -> res) = a->b->c->d->e->f -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f) = fun a b c d e f
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f:.g -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f:.g -> res) = a->b->c->d->e->f->g -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f:.g) = fun a b c d e f g
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h -> res) = a->b->c->d->e->f->g->h -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h) = fun a b c d e f g h
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i -> res) = a->b->c->d->e->f->g->h->i -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i) = fun a b c d e f g h i
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j -> res) = a->b->c->d->e->f->g->h->i->j -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j) = fun a b c d e f g h i j
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k -> res) = a->b->c->d->e->f->g->h->i->j->k -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k) = fun a b c d e f g h i j k
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l -> res) = a->b->c->d->e->f->g->h->i->j->k->l -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l) = fun a b c d e f g h i j k l
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m -> res) = a->b->c->d->e->f->g->h->i->j->k->l->m -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m) = fun a b c d e f g h i j k l m
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n -> res) = a->b->c->d->e->f->g->h->i->j->k->l->m->n -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n) = fun a b c d e f g h i j k l m n
  {-# INLINE apply #-}

instance Apply (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n:.o -> res) where
  type Fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n:.o -> res) = a->b->c->d->e->f->g->h->i->j->k->l->m->n->o -> res
  apply fun (ArgZ:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n:.o) = fun a b c d e f g h i j k l m n o
  {-# INLINE apply #-}

