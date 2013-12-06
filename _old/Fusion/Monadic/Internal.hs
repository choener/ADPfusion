{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_HADDOCK hide #-}

-- | The internal working of ADPfusion. All combinator applications are turned
-- into efficient code during compile time.
--
-- If you have a data structure to be used as an argument in a combinator
-- chain, derive an instance 'ExtractValue', 'StreamGen', and 'PreStreamGen'.
--
-- NOTE: If this doesn't happen, it is a possible bug, or GHC changed its
-- optimizer (like with GHC 7.2 -> 7.4).
--
-- TODO If possible, instance generation will be using the Generics system in
-- the future.

module ADP.Fusion.Monadic.Internal where

import Control.Monad.Primitive
import Control.Monad.ST
import Data.List (intersperse)
import Data.Primitive.Types
import Data.Vector.Fusion.Stream.Size
import Data.Array.Repa.Index
import Data.Array.Repa.Shape
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Text.Printf

import qualified Data.PrimitiveArray as PA
--import qualified Data.PrimitiveArray.Zero.Unboxed as ZU
import qualified Data.PrimitiveArray.Zero as Z


{-
-- * StreamGen

-- | Generate stream from either one (DIM2 -> m cnt) or some combination of
-- terminals derived from uses of nextTo.

class Monad m => StreamGen m t r | t -> r where
  streamGen :: t -> DIM2 -> S.Stream m r

#define mkStreamGen(cnt) \
instance (Monad m, ExtractValue m (cnt), Asor (cnt) ~ k, Elem (cnt) ~ elm) \
=> StreamGen m (cnt) (DIM2,Z:.k,Z:.elm) where { \
  {-# INLINE streamGen #-} \
;  streamGen x ij = extractStreamLast x $ preStreamGen x ij }

mkStreamGen(DIM2 -> Scalar elm)
mkStreamGen(DIM2 -> ScalarM elm)
mkStreamGen(DIM2 -> Vect elm)
mkStreamGen(DIM2 -> VectM elm)
mkStreamGen(ZU.MArr0 s sh elm)
mkStreamGen(ZU.Arr0 sh elm)

mkStreamGen(Z.MArr0 s sh (VU.Vector elm))
mkStreamGen(Z.Arr0 sh (VU.Vector elm))

-- | two or more elements combined by NextTo (~~~), "xs" as anything, "ys" is
-- monadic.

instance
  ( Monad m
  , ExtractValue m ys, Asor ys ~ cY, Elem ys ~ eY
  , PreStreamGen m (Box mk step xs ys) (idx:.Int,adx:.cX,arg:.eX)
  , Idx2 _idx ~ idx
  ) => StreamGen m (Box mk step xs ys) (idx:.Int,adx:.cX:.cY,arg:.eX:.eY) where
  streamGen (Box mk step xs ys) ij
    = extractStreamLast ys
    $ preStreamGen (Box mk step xs ys) ij
  {-# INLINE streamGen #-}



-- * PreStreamGen

-- | Required by most 'StreamGen' instances just before 'extractStreamLast' is
-- called.

class Monad m => PreStreamGen m s q | s -> q where
  preStreamGen
    :: s      -- ^ the composite type of the arguments
    -> DIM2   -- ^ the original index @(Z:.i:.j)@
    -> S.Stream m q -- ^ the stream we get out of it

-- | Creates the single step on the left which does nothing more then set the
-- outermost indices to (i,j). This does not use the alpha/omega's

singlePreStreamGen ij = S.unfoldr step ij where
  {-# INLINE step #-}
  step (Z:.i:.j)
    | i<=j      = Just ((Z:.i:.j ,Z,Z), Z:.j+1:.j)
    | otherwise = Nothing
{-# INLINE singlePreStreamGen #-}

#define mkPreStreamGen(s) \
instance (Monad m) => PreStreamGen m (s) (DIM2,Z,Z) where { \
  {-# INLINE preStreamGen #-} \
;  preStreamGen _ = singlePreStreamGen }

mkPreStreamGen(DIM2 -> Scalar elm)
mkPreStreamGen(DIM2 -> ScalarM elm)
mkPreStreamGen(DIM2 -> Vect elm)
mkPreStreamGen(DIM2 -> VectM elm)
mkPreStreamGen(ZU.MArr0 s sh elm)
mkPreStreamGen(ZU.Arr0 sh elm)

mkPreStreamGen(Z.MArr0 s sh (VU.Vector elm))
mkPreStreamGen(Z.Arr0 sh (VU.Vector elm))

-- | the first two arguments from nextTo, monadic xs.

instance ( Monad m
         , ExtractValue m xs, Asor xs ~ cX, Elem xs ~ eX
         , PreStreamGen m xs xsStack
         , (idxX,adxX,argX) ~ xsStack
         , (z0:.Int:.Int) ~ idxX
         , ((idxX,adxX,argX) -> m (idxX:.Int,adxX,argX)) ~ mk
         , ((idxX:.Int,adxX,argX) -> m (S.Step (idxX:.Int,adxX,argX) (idxX:.Int,adxX,argX))) ~ step
         ) => PreStreamGen m (Box mk step xs ys) (idxX:.Int,adxX:.cX,argX:.eX) where
  preStreamGen (Box mk step xs ys) ij
    = extractStream xs
    $ S.flatten mk step Unknown
    $ preStreamGen xs ij
  {-# INLINE preStreamGen #-}

-- | Pre-stream generation for deeply nested boxes.

instance
  ( Monad m
  , ExtractValue m xs, Asor xs ~ cX, Elem xs ~ eX
  , PreStreamGen m (Box box2 box3 box1 xs) xsStack
  , (idxX,adxX,argX) ~ xsStack
  , (z0:.Int:.Int) ~ idxX
  , ((idxX,adxX,argX) -> m (idxX:.Int,adxX,argX)) ~ mk
  , ((idxX:.Int,adxX,argX) -> m (S.Step (idxX:.Int,adxX,argX) (idxX:.Int,adxX,argX))) ~ step
  ) => PreStreamGen m (Box mk step (Box box2 box3 box1 xs) ys) (idxX:.Int,adxX:.cX,argX:.eX) where
  preStreamGen (Box mk step box@(Box _ _ _ xs) ys) ij
    = extractStream xs
    $ S.flatten mk step Unknown
    $ preStreamGen box ij
  {-# INLINE preStreamGen #-}



-- * ExtractValue: extract values from data structures.

class (Monad m) => ExtractValue m cnt where
  type Asor cnt :: *
  type Elem cnt :: *
  extractValue  :: ()
                => cnt
                -> DIM2
                -> Asor cnt
                -> m (Elem cnt)
  extractStream :: ()
                => cnt
                -> S.Stream m (Idx3 z,astack,vstack)
                -> S.Stream m (Idx3 z,astack:.Asor cnt,vstack:.Elem cnt)
  extractStreamLast :: ()
                    => cnt
                    -> S.Stream m (Idx2 z,astack,vstack)
                    -> S.Stream m (Idx2 z,astack:.Asor cnt,vstack:.Elem cnt)

-- | Mutable arrays.

instance
  ( PrimMonad m
  , VU.Unbox elm
  , PrimState m ~ s
  , DIM2 ~ sh
  ) => ExtractValue m (ZU.MArr0 s sh elm) where
  type Asor (ZU.MArr0 s sh elm) = Z
  type Elem (ZU.MArr0 s sh elm) = elm
  extractValue cnt ij z = do
    x <- PA.readM cnt ij
    x `seq` return x
  extractStream cnt stream = S.mapM addElm stream where
    addElm (z:.k:.x:.l, astack, vstack) = do
      vadd <- PA.readM cnt (Z:.k:.x)
      vadd `seq` return (z:.k:.x:.l, astack:.Z, vstack :. vadd)
  extractStreamLast sngl stream = S.mapM addElm stream where
    addElm (z:.k:.x, astack, vstack) = do
      vadd <- PA.readM sngl (Z:.k:.x)
      vadd `seq` return (z:.k:.x, astack:.Z, vstack:.vadd)
  {-# INLINE extractValue #-}
  {-# INLINE extractStream #-}
  {-# INLINE extractStreamLast #-}

-- | Immutable arrays.

instance
  ( Monad m
  , VU.Unbox elm
  , DIM2 ~ sh
  ) => ExtractValue m (ZU.Arr0 sh elm) where
  type Asor (ZU.Arr0 sh elm) = Z
  type Elem (ZU.Arr0 sh elm) = elm
  extractValue cnt ij z = do
    let x = PA.index cnt ij
    x `seq` return x
  extractStream cnt stream = S.map addElm stream where
    addElm (z:.k:.x:.l, astack, vstack) = let vadd = PA.index cnt (Z:.k:.x) in
      vadd `seq` (z:.k:.x:.l, astack:.Z, vstack :. vadd)
  extractStreamLast cnt stream = S.map addElm stream where
    addElm (z:.k:.x, astack, vstack) = let vadd = PA.index cnt (Z:.k:.x) in
      vadd `seq` (z:.k:.x, astack:.Z, vstack:.vadd)
  {-# INLINE extractValue #-}
  {-# INLINE extractStream #-}
  {-# INLINE extractStreamLast #-}

-- | Function with 'Scalar' return value.

instance
  ( Monad m
  ) => ExtractValue m (DIM2 -> Scalar elm) where
  type Asor (DIM2 -> Scalar elm) = Z
  type Elem (DIM2 -> Scalar elm) = elm
  extractValue cnt ij z = do
    let Scalar x = cnt ij
    x `seq` return x
  extractStream cnt stream = S.map addElm stream where
    addElm (z:.k:.x:.l, astack, vstack) = let Scalar vadd = cnt (Z:.k:.x) in
      vadd `seq` (z:.k:.x:.l, astack:.Z, vstack :. vadd)
  extractStreamLast cnt stream = S.map addElm stream where
    addElm (z:.k:.x, astack, vstack) = let Scalar vadd = cnt (Z:.k:.x) in
      vadd `seq` (z:.k:.x, astack:.Z, vstack:.vadd)
  {-# INLINE extractValue #-}
  {-# INLINE extractStream #-}
  {-# INLINE extractStreamLast #-}

-- | Function with monadic 'Scalar' return value.

instance
  ( Monad m
  ) => ExtractValue m (DIM2 -> ScalarM (m elm)) where
  type Asor (DIM2 -> ScalarM (m elm)) = Z
  type Elem (DIM2 -> ScalarM (m elm)) = elm
  extractValue cnt ij z = do
    let ScalarM x' = cnt ij
    x <- x'
    x `seq` return x
  extractStream cnt stream = S.mapM addElm stream where
    addElm (z:.k:.x:.l, astack, vstack) = do
      let ScalarM vadd' = cnt (Z:.k:.x)
      vadd <- vadd'
      vadd `seq` return (z:.k:.x:.l, astack:.Z, vstack :. vadd)
  extractStreamLast cnt stream = S.mapM addElm stream where
    addElm (z:.k:.x, astack, vstack) = do
      let ScalarM vadd' = cnt (Z:.k:.x)
      vadd <- vadd'
      vadd `seq` return (z:.k:.x, astack:.Z, vstack:.vadd)
  {-# INLINE extractValue #-}
  {-# INLINE extractStream #-}
  {-# INLINE extractStreamLast #-}

-- | This instance is a bit crazy, since the accessor is the current stream
-- itself. No idea how efficient this is (need to squint at CORE), but I plan
-- to use it for backtracking only.
--
-- TODO Using this instance tends to break to optimizer ;-) -- don't use it
-- yet!

instance
  ( Monad m
  ) => ExtractValue m (DIM2 -> S.Stream m elm) where
  type Asor (DIM2 -> S.Stream m elm) = S.Stream m elm
  type Elem (DIM2 -> S.Stream m elm) = elm
  extractValue cnt ij z = error "this function is not well-defined for these streams"
  extractStream cnt stream = S.flatten mk step Unknown $ stream where
    mk (z:.k:.l:.j,as,vs) = do
      let strm = cnt (Z:.k:.l)
      return (z:.k:.l:.j,as:.strm,vs)
    step (idx,as:.strm,vs) = do
      isNull <- S.null strm
      if isNull
      then return $ S.Done
      else do hd <- S.head strm
              hd `seq` return $ S.Yield (idx,as:.strm,vs:.hd) (idx,as:.S.tail strm,vs)
  extractStreamLast cnt stream = S.flatten mk step Unknown $ stream where
    mk (z:.l:.j,as,vs) = do
      let strm = cnt (Z:.l:.j)
      return (z:.l:.j,as:.strm,vs)
    step (idx,as:.strm,vs) = do
      isNull <- S.null strm
      if isNull
      then return $ S.Done
      else do hd <- S.head strm
              hd `seq` return $ S.Yield (idx,as:.strm,vs:.hd) (idx,as:.S.tail strm,vs)
  {-# INLINE extractValue #-}
  {-# INLINE extractStream #-}
  {-# INLINE extractStreamLast #-}

-- | Instance of boxed array with vector-valued cells. We assume that we want
-- to store multiple results for each cell. If the intent is to store one
-- scalar result, use the 'Scalar' wrapper.

instance
  ( PrimMonad m
  , Prim elm
  , VU.Unbox elm
  , PrimState m ~ s
  , DIM2 ~ sh
  ) => ExtractValue m (Z.MArr0 s sh (VU.Vector elm)) where
  type Asor (Z.MArr0 s sh (VU.Vector elm)) = Int
  type Elem (Z.MArr0 s sh (VU.Vector elm)) = elm
  extractValue cnt ij z = do
    x <- PA.readM cnt ij
    let y = x `VU.unsafeIndex` z
    y `seq` return y
  extractStream cnt stream = S.flatten mk step Unknown $ stream where
    mk (idx,as,vs) = return (idx,as:.0,vs)
    step (z:.k:.l:.j,as:.a,vs) = do
      x <- PA.readM cnt (Z:.k:.l)
      case (x VU.!? a) of
        Just v  -> v `seq` return $ S.Yield (z:.k:.l:.j,as:.a,vs:.v) (z:.k:.l:.j,as:.(a+1),vs)
        Nothing -> return $ S.Done
  extractStreamLast cnt stream = S.flatten mk step Unknown $ stream where
    mk (idx,as,vs) = return (idx,as:.0,vs)
    step (z:.l:.j,as:.a,vs) = do
      x <- PA.readM cnt (Z:.l:.j)
      case (x VU.!? a) of
        Just v  -> v `seq` return $ S.Yield (z:.l:.j,as:.a,vs:.v) (z:.l:.j,as:.(a+1),vs)
        Nothing -> return $ S.Done
  {-# INLINE extractValue #-}
  {-# INLINE extractStream #-}
  {-# INLINE extractStreamLast #-}

-- | vector-based cells

instance
  ( Monad m
  , Prim elm
  , VU.Unbox elm
  , DIM2 ~ sh
  ) => ExtractValue m (Z.Arr0 sh (VU.Vector elm)) where
  type Asor (Z.Arr0 sh (VU.Vector elm)) = Int
  type Elem (Z.Arr0 sh (VU.Vector elm)) = elm
  extractValue cnt ij z = do
    let x = PA.index cnt ij
    let y = x `VU.unsafeIndex` z
    y `seq` return y
  extractStream cnt stream = S.flatten mk step Unknown $ stream where
    mk (idx,as,vs) = return (idx,as:.0,vs)
    step (z:.k:.l:.j,as:.a,vs) = do
      let x = PA.index cnt (Z:.k:.l)
      case (x VU.!? a) of
        Just v  -> v `seq` return $ S.Yield (z:.k:.l:.j,as:.a,vs:.v) (z:.k:.l:.j,as:.(a+1),vs)
        Nothing -> return $ S.Done
  extractStreamLast cnt stream = S.flatten mk step Unknown $ stream where
    mk (idx,as,vs) = return (idx,as:.0,vs)
    step (z:.l:.j,as:.a,vs) = do
      let x = PA.index cnt (Z:.l:.j)
      case (x VU.!? a) of
        Just v  -> v `seq` return $ S.Yield (z:.l:.j,as:.a,vs:.v) (z:.l:.j,as:.(a+1),vs)
        Nothing -> return $ S.Done
  {-# INLINE extractValue #-}
  {-# INLINE extractStream #-}
  {-# INLINE extractStreamLast #-}
-}

-- * Apply function 'f' with arguments on a stack 'x'.
--
-- NOTE look at the end of this part for mkApply before writing instances by
-- hand... ;-)

class Apply x where
  type Fun x :: *
  apply :: Fun x -> x

instance Apply (Z:.a -> res) where
  type Fun (Z:.a -> res) = a -> res
  apply fun (Z:.a) = fun a
  {-# INLINE apply #-}

instance Apply (Z:.a:.b -> res) where
  type Fun (Z:.a:.b -> res) = a->b -> res
  apply fun (Z:.a:.b) = fun a b
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c -> res) where
  type Fun (Z:.a:.b:.c -> res) = a->b->c -> res
  apply fun (Z:.a:.b:.c) = fun a b c
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d -> res) where
  type Fun (Z:.a:.b:.c:.d -> res) = a->b->c->d -> res
  apply fun (Z:.a:.b:.c:.d) = fun a b c d
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e -> res) where
  type Fun (Z:.a:.b:.c:.d:.e -> res) = a->b->c->d->e -> res
  apply fun (Z:.a:.b:.c:.d:.e) = fun a b c d e
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f -> res) = a->b->c->d->e->f -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f) = fun a b c d e f
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g -> res) = a->b->c->d->e->f->g -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g) = fun a b c d e f g
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h -> res) = a->b->c->d->e->f->g->h -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h) = fun a b c d e f g h
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i -> res) = a->b->c->d->e->f->g->h->i -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i) = fun a b c d e f g h i
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j -> res) = a->b->c->d->e->f->g->h->i->j -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j) = fun a b c d e f g h i j
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k -> res) = a->b->c->d->e->f->g->h->i->j->k -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k) = fun a b c d e f g h i j k
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l -> res) = a->b->c->d->e->f->g->h->i->j->k->l -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l) = fun a b c d e f g h i j k l
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m -> res) = a->b->c->d->e->f->g->h->i->j->k->l->m -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m) = fun a b c d e f g h i j k l m
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n -> res) = a->b->c->d->e->f->g->h->i->j->k->l->m->n -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n) = fun a b c d e f g h i j k l m n
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n:.o -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n:.o -> res) = a->b->c->d->e->f->g->h->i->j->k->l->m->n->o -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n:.o) = fun a b c d e f g h i j k l m n o
  {-# INLINE apply #-}

{-
mkApply to = do
  let xs    = ['a' .. to]
  let args  = concat . (":.":) . intersperse ":." . map (:[]) $ xs
  let arga  = concat . intersperse "->" . map (:[]) $ xs
  let args' = intersperse ' ' xs
  printf "instance Apply (Z%s -> res) where\n" args
  printf "  type Fun (Z%s -> res) = %s -> res\n" args arga
  printf "  apply fun (Z%s) = fun %s\n" args args'
  printf "  {-# INLINE apply #-}\n"
-}



-- * helper stuff

data Box mk step xs ys = Box mk step xs ys

type Idx3 z = z:.Int:.Int:.Int

type Idx2 z = z:.Int:.Int



-- * wrappers for functions instead of arrays as arguments. It can be much
-- cheaper in terms of writing code to just provide a function @DIM2 -> Scalar
-- a@ instead of writing instances for your data structure.

newtype Scalar a = Scalar {unScalar :: a}

newtype ScalarM a = ScalarM {unScalarM :: a}

newtype Vect a = Vect {unVect :: a}

newtype VectM a = VectM {unVectM :: a}
