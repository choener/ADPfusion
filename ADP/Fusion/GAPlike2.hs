{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | 
--
-- HINTS for writing your own (Non-) terminals:
--
-- - ALWAYS provide types for local functions of 'mkStream' and
-- 'mkStreamInner'. Otherwise stream-fusion gets confused and doesn't optimize.
-- (Observable in core by looking for 'Left', 'RIght' constructors and 'SPEC'
-- constructors.

module ADP.Fusion.GAPlike2 where

import Control.Monad.Primitive
import Control.Monad.ST
import Data.List (intersperse)
import Data.Primitive
import Data.Vector.Fusion.Stream.Size
import GHC.Prim (Constraint)
import qualified Data.Vector.Fusion.Stream as SP
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Text.Printf
import Control.Exception (assert)

import Data.PrimitiveArray
import Data.PrimitiveArray.Unboxed.VectorZero as UVZ
import Data.PrimitiveArray.Unboxed.Zero as UZ
import "PrimitiveArray" Data.Array.Repa.Index
import "PrimitiveArray" Data.Array.Repa.Shape
import qualified Data.PrimitiveArray as PA



-- * The required type classes. Each class does its own thing.

-- | The 'Build' class. Combines the arguments into a stack before they are
-- turned into a stream.
--
--
--
-- To use, simply write "instance Build MyDataCtor" as we have sensible default
-- instances.

class Build x where
  -- | The stack of arguments we are building.
  type BuildStack x :: *
  -- | The default is for the left-most element.
  type BuildStack x = None :. x
  -- | Given an element, create the stack.
  build :: x -> BuildStack x
  -- | Default for the left-most element.
  default build :: (BuildStack x ~ (None :. x)) => x -> BuildStack x
  build x = None :. x
  {-# INLINE build #-}

-- | The stream element. Creates a type-level recursive data type containing
-- the extracted arguments.

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

-- | Given the arguments, creates a stream of 'StreamElement's.

class (StreamConstraint x) => MkStream m x where
  type StreamConstraint x :: Constraint
  type StreamConstraint x = ()
  mkStream      :: (StreamConstraint x) => x -> (Int,Int) -> S.Stream m (StreamElm x)
  mkStreamInner :: (StreamConstraint x) => x -> (Int,Int) -> S.Stream m (StreamElm x)



-- * Terminates the stack of arguments

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



-- * A single character terminal. Using unboxed vector to hold the input.

data Chr e = Chr !(VU.Vector e)

instance Build (Chr e)

instance (StreamElement x) => StreamElement (x:.Chr e) where
  data StreamElm (x:.Chr e) = SeChr !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Chr e) = Int
  type StreamArg (x:.Chr e) = StreamArg x :. e
  getTopIdx (SeChr _ k _) = k
  getArg (SeChr x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

-- |
--
-- TODO I think, we can rewrite both versions to use S.map instead of S.flatten.

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



-- * Empty and non-empty tables.
--
-- TODO This will probably become more funny with triangular tables ...

-- | empty subwords allowed

data E

-- | only non-empty subwords

data N

-- | Used by the instances below for index calculations.

class TblType tt where
  initDeltaIdx :: tt -> Int

instance TblType E where
  initDeltaIdx _ = 0
  {-# INLINE initDeltaIdx #-}

instance TblType N where
  initDeltaIdx _ = 1
  {-# INLINE initDeltaIdx #-}

-- ** Immutable tables

data Tbl c es = Tbl !es

instance Build (Tbl c es)

instance (StreamElement x, PrimArrayOps arr DIM2 e, TblType c) => StreamElement (x:.Tbl c (arr DIM2 e)) where
  data StreamElm    (x:.Tbl c (arr DIM2 e)) = SeTbl !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Tbl c (arr DIM2 e)) = Int
  type StreamArg    (x:.Tbl c (arr DIM2 e)) = StreamArg x :. e
  getTopIdx (SeTbl _ k _) = k
  getArg    (SeTbl x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, PrimArrayOps arr DIM2 e, TblType c) => MkStream m (x:.Tbl c (arr DIM2 e)) where
  -- | The outer stream function assumes that mkStreamInner generates a valid
  -- stream that does not need to be checked. (This should always be true!).
  -- The table entry to read is [k,j], as we supposedly are generating the
  -- outermost stream. Even more "outermost" streams will have changed 'j'
  -- beforehand. 'mkStream' should only ever be used if 'j' can be fixed.
  mkStream (x:.Tbl t) (i,j) = S.map step $ mkStreamInner x (i,j - initDeltaIdx (undefined :: c)) where
    step :: StreamElm x -> StreamElm (x:.Tbl c (arr DIM2 e))
    step x = let k = getTopIdx x in SeTbl x j (t PA.! (Z:.k:.j))
    {-# INLINE step #-}
  -- | The inner stream will, in each step, check if the current subword [k,l]
  -- (forall l>=k) is valid and terminate the stream once l>j.
  mkStreamInner (x:.Tbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x + initDeltaIdx (undefined :: c))
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Tbl c (arr DIM2 e))))
    step (x,l)
      | l<=j      = return $ S.Yield (SeTbl x l (t PA.! (Z:.k:.l))) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}

-- ** Mutable tables in some monad.

data MTbl c es = MTbl !es

instance Build (MTbl c es)

instance (StreamElement x, MPrimArrayOps marr DIM2 e, TblType c) => StreamElement (x:.MTbl c (marr s DIM2 e)) where
  data StreamElm    (x:.MTbl c (marr s DIM2 e)) = SeMTbl !(StreamElm x) !Int !e
  type StreamTopIdx (x:.MTbl c (marr s DIM2 e)) = Int
  type StreamArg    (x:.MTbl c (marr s DIM2 e)) = StreamArg x :. e
  getTopIdx (SeMTbl _ k _) = k
  getArg    (SeMTbl x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, PrimMonad m, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, MPrimArrayOps marr DIM2 e, TblType c, s ~ PrimState m) => MkStream m (x:.MTbl c (marr s DIM2 e)) where
  -- | The outer stream function assumes that mkStreamInner generates a valid
  -- stream that does not need to be checked. (This should always be true!).
  -- The table entry to read is [k,j], as we supposedly are generating the
  -- outermost stream. Even more "outermost" streams will have changed 'j'
  -- beforehand. 'mkStream' should only ever be used if 'j' can be fixed.
  mkStream (x:.MTbl t) (i,j) = S.mapM step $ mkStreamInner x (i,j - initDeltaIdx (undefined :: c)) where
    step :: StreamElm x -> m (StreamElm (x:.MTbl c (marr s DIM2 e)))
    step x = let k = getTopIdx x in PA.readM t (Z:.k:.j) >>= \e -> return $ SeMTbl x j e
    {-# INLINE step #-}
  -- | The inner stream will, in each step, check if the current subword [k,l]
  -- (forall l>=k) is valid and terminate the stream once l>j.
  mkStreamInner (x:.MTbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x + initDeltaIdx (undefined :: c))
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.MTbl c (marr s DIM2 e))))
    step (x,l)
      | l<=j      = readM t (Z:.k:.l) >>= \e -> return $ S.Yield (SeMTbl x l e) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}

-- ** Some convenience functions.

tNtoE :: Tbl N x -> Tbl E x
tNtoE (Tbl x) = Tbl x
{-# INLINE tNtoE #-}

tEtoN :: Tbl E x -> Tbl N x
tEtoN (Tbl x) = Tbl x
{-# INLINE tEtoN #-}



-- * Parses an empty subword.

-- | The empty subword. Can not be part of a more complex RHS for obvious
-- reasons: S -> E S doesn't make sense. Used in some grammars as the base
-- case.

data Empty = Empty

instance Build Empty where
  type BuildStack Empty = Empty
  build c = c
  {-# INLINE build #-}

instance StreamElement (Empty) where
  data StreamElm    Empty = SeEmpty !Int
  type StreamTopIdx Empty = Int
  type StreamArg    Empty = ArgZ :. ()
  getTopIdx (SeEmpty k) = k
  getArg    (SeEmpty _) = ArgZ :. ()
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m) => MkStream m (Empty) where
  mkStream Empty (i,j) = S.unfoldr step i where
    step k
      | k==j      = Just (SeEmpty k, j+1)
      | otherwise = Nothing
    {-# INLINE step #-}
  mkStreamInner = error "undefined for Empty"
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}



data RestrictedRegion e = RRegion !Int !Int !(VU.Vector e)

instance Build (RestrictedRegion e)

instance (StreamElement x) => StreamElement (x:.RestrictedRegion e) where
  data StreamElm (x:.RestrictedRegion e) = SeResRegion !(StreamElm x) !Int (VU.Vector e)
  type StreamTopIdx (x:.RestrictedRegion e) = Int
  type StreamArg (x:.RestrictedRegion e) = StreamArg x :. (VU.Vector e)
  getTopIdx (SeResRegion _ k _) = k
  getArg (SeResRegion x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.RestrictedRegion e) where
  mkStream (x:.RRegion minR maxR xs) (i,j) = S.flatten mk step Unknown $ mkStream x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.RestrictedRegion e)))
    step (x,k)
      | k+minR <= j && k+maxR >= j = return $ S.Yield (SeResRegion x k (VU.unsafeSlice k (max maxR (j-k)) xs)) (x,j+1)
      | otherwise = return S.Done
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  mkStreamInner (x:.RRegion minR maxR xs) (i,j) = S.flatten mk step Unknown $ mkStream x (i,j) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x + minR)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.RestrictedRegion e)))
    step (x,l)
      | l<=j && (l-k)<=maxR = return $ S.Yield (SeResRegion x l (VU.unsafeSlice k (l-k) xs)) (x,j+1)
      | otherwise           = return S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStreamInner #-}



-- * Build complex stacks

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

infixl 6 ..@
(..@) s h ij = h ij $ s ij
{-# INLINE (..@) #-}

infixl 9 ~~
(~~) = (,)
{-# INLINE (~~) #-}

infixl 9 %
(%) = (,)
{-# INLINE (%) #-}







-- * Apply function 'f' in '(<<<)'

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



