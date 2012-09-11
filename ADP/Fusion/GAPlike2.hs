{-# LANGUAGE TemplateHaskell #-}
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

-- ** by default, every table should be wrapped. Instances for wrapped two-dim.
-- tables with underlying primitive or unboxed-vector instances.

-- | empty subwords allowed

data E

-- | only non-empty subwords

data N

-- | Phantom typing the table.

data Tbl c es = Tbl !es

-- | Build all variants of 'Tbl's.

instance Build (Tbl typ cnt) where
  type BuildStack (Tbl typ cnt) = None:.Tbl typ cnt
  build tbl = None:.tbl

-- *** 2D-table of immutable data.

instance (StreamElement x) => StreamElement (x:.Tbl E (UVZ.Arr0 DIM2 e)) where
  data StreamElm    (x:.Tbl E (UVZ.Arr0 DIM2 e)) = SeTblEuvzA !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Tbl E (UVZ.Arr0 DIM2 e)) = Int
  type StreamArg    (x:.Tbl E (UVZ.Arr0 DIM2 e)) = StreamArg x :. e
  getTopIdx (SeTblEuvzA _ k _) = k
  getArg    (SeTblEuvzA x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.Tbl E (UVZ.Arr0 DIM2 e)) where
  -- | The outer stream function assumes that mkStreamInner generates a valid
  -- stream that does not need to be checked. (This should always be true!).
  -- The table entry to read is [k,j], as we supposedly are generating the
  -- outermost stream. Even more "outermost" streams will have changed 'j'
  -- beforehand. 'mkStream' should only ever be used if 'j' can be fixed.
  mkStream (x:.Tbl t) (i,j) = S.map step $ mkStreamInner x (i,j) where
    step :: StreamElm x -> StreamElm (x:.Tbl E (UVZ.Arr0 DIM2 e))
    step x = let k = getTopIdx x in SeTblEuvzA x j (t PA.! (Z:.k:.j))
    {-# INLINE step #-}
  -- | The inner stream will, in each step, check if the current subword [k,l]
  -- (forall l>=k) is valid and terminate the stream once l>j.
  mkStreamInner (x:.Tbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Tbl E (UVZ.Arr0 DIM2 e))))
    step (x,l)
      | l<=j      = return $ S.Yield (SeTblEuvzA x l (t PA.! (Z:.k:.l))) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}

instance (StreamElement x) => StreamElement (x:.Tbl E (UZ.Arr0 DIM2 e)) where
  data StreamElm    (x:.Tbl E (UZ.Arr0 DIM2 e)) = SeTblEuzA !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Tbl E (UZ.Arr0 DIM2 e)) = Int
  type StreamArg    (x:.Tbl E (UZ.Arr0 DIM2 e)) = StreamArg x :. e
  getTopIdx (SeTblEuzA _ k _) = k
  getArg    (SeTblEuzA x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, Prim e) => MkStream m (x:.Tbl E (UZ.Arr0 DIM2 e)) where
  mkStream (x:.Tbl t) (i,j) = S.map step $ mkStreamInner x (i,j) where
    step :: StreamElm x -> StreamElm (x:.Tbl E (UZ.Arr0 DIM2 e))
    step x = let k = getTopIdx x in SeTblEuzA x j (t PA.! (Z:.k:.j))
    {-# INLINE step #-}
  mkStreamInner (x:.Tbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Tbl E (UZ.Arr0 DIM2 e))))
    step (x,l)
      | l<=j      = return $ S.Yield (SeTblEuzA x l (t PA.! (Z:.k:.l))) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}

instance (StreamElement x) => StreamElement (x:.Tbl E (UVZ.MArr0 s DIM2 e)) where
  data StreamElm    (x:.Tbl E (UVZ.MArr0 s DIM2 e)) = SeTblEuvzMA !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Tbl E (UVZ.MArr0 s DIM2 e)) = Int
  type StreamArg    (x:.Tbl E (UVZ.MArr0 s DIM2 e)) = StreamArg x :. e
  getTopIdx (SeTblEuvzMA _ k _) = k
  getArg    (SeTblEuvzMA x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.Tbl E (UVZ.MArr0 s DIM2 e)) where
  mkStream (x:.Tbl t) (i,j) = S.mapM step $ mkStreamInner x (i,j) where
    step :: StreamElm x -> m (StreamElm (x:.Tbl E (UVZ.MArr0 s DIM2 e)))
    step x = let k = getTopIdx x in PA.readM t (Z:.k:.j) >>= \e -> return $ SeTblEuvzMA x j e
    {-# INLINE step #-}
  mkStreamInner (x:.Tbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Tbl E (UVZ.MArr0 s DIM2 e))))
    step (x,l)
      | l<=j      = readM t (Z:.k:.l) >>= \e -> return $ S.Yield (SeTblEuvzMA x l e) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}

instance (StreamElement x) => StreamElement (x:.Tbl E (UZ.MArr0 s DIM2 e)) where
  data StreamElm    (x:.Tbl E (UZ.MArr0 s DIM2 e)) = SeTblEuzMA !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Tbl E (UZ.MArr0 s DIM2 e)) = Int
  type StreamArg    (x:.Tbl E (UZ.MArr0 s DIM2 e)) = StreamArg x :. e
  getTopIdx (SeTblEuzMA _ k _) = k
  getArg    (SeTblEuzMA x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, Prim e) => MkStream m (x:.Tbl E (UZ.MArr0 s DIM2 e)) where
  mkStream (x:.Tbl t) (i,j) = S.mapM step $ mkStreamInner x (i,j) where
    step :: StreamElm x -> m (StreamElm (x:.Tbl E (UZ.MArr0 s DIM2 e)))
    step x = let k = getTopIdx x in PA.readM t (Z:.k:.j) >>= \e -> return $ SeTblEuzMA x j e
    {-# INLINE step #-}
  mkStreamInner (x:.Tbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Tbl E (UZ.MArr0 s DIM2 e))))
    step (x,l)
      | l<=j      = readM t (Z:.k:.l) >>= \e -> return $ S.Yield (SeTblEuzMA x l e) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}


-- *** non-empty.

instance (StreamElement x) => StreamElement (x:.Tbl N (UVZ.Arr0 DIM2 e)) where
  data StreamElm    (x:.Tbl N (UVZ.Arr0 DIM2 e)) = SeTblNuvzA !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Tbl N (UVZ.Arr0 DIM2 e)) = Int
  type StreamArg    (x:.Tbl N (UVZ.Arr0 DIM2 e)) = StreamArg x :. e
  getTopIdx (SeTblNuvzA _ k _) = k
  getArg    (SeTblNuvzA x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.Tbl N (UVZ.Arr0 DIM2 e)) where
  -- | The As we reduce 'j' by '1' for the inner stream, the result should be
  -- an available subword [k,j] of at least size 1.
  mkStream (x:.Tbl t) (i,j) = S.map step $ mkStreamInner x (i,j-1) where
    step :: StreamElm x -> StreamElm (x:.Tbl N (UVZ.Arr0 DIM2 e))
    step x = let k = getTopIdx x; e = t PA.! (Z:.k:.j) in assert (i<=k && k<j) $ e `seq` SeTblNuvzA x j e
    {-# INLINE step #-}
  -- | Inner stream, run an index l between k<l<=j. The subword we generate is [k,l].
  mkStreamInner (x:.Tbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x +1)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Tbl N (UVZ.Arr0 DIM2 e))))
    step (x,l)
      | l<=j      = let e = t PA.! (Z:.k:.l) in assert (i<=k) . return $ e `seq` S.Yield (SeTblNuvzA x l e) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}

instance (StreamElement x) => StreamElement (x:.Tbl N (UZ.Arr0 DIM2 e)) where
  data StreamElm    (x:.Tbl N (UZ.Arr0 DIM2 e)) = SeTblNuzA !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Tbl N (UZ.Arr0 DIM2 e)) = Int
  type StreamArg    (x:.Tbl N (UZ.Arr0 DIM2 e)) = StreamArg x :. e
  getTopIdx (SeTblNuzA _ k _) = k
  getArg    (SeTblNuzA x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, Prim e) => MkStream m (x:.Tbl N (UZ.Arr0 DIM2 e)) where
  mkStream (x:.Tbl t) (i,j) = S.map step $ mkStreamInner x (i,j-1) where
    step :: StreamElm x -> StreamElm (x:.Tbl N (UZ.Arr0 DIM2 e))
    step x = let k = getTopIdx x; e = t PA.! (Z:.k:.j) in assert (i<=k && k<j) $ e `seq` SeTblNuzA x j e
    {-# INLINE step #-}
  mkStreamInner (x:.Tbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x +1)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Tbl N (UZ.Arr0 DIM2 e))))
    step (x,l)
      | l<=j      = let e = t PA.! (Z:.k:.l) in assert (i<=k) . return $ e `seq` S.Yield (SeTblNuzA x l e) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}

instance (StreamElement x) => StreamElement (x:.Tbl N (UVZ.MArr0 s DIM2 e)) where
  data StreamElm    (x:.Tbl N (UVZ.MArr0 s DIM2 e)) = SeTblNuvzMA !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Tbl N (UVZ.MArr0 s DIM2 e)) = Int
  type StreamArg    (x:.Tbl N (UVZ.MArr0 s DIM2 e)) = StreamArg x :. e
  getTopIdx (SeTblNuvzMA _ k _) = k
  getArg    (SeTblNuvzMA x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, VU.Unbox e) => MkStream m (x:.Tbl N (UVZ.MArr0 s DIM2 e)) where
  mkStream (x:.Tbl t) (i,j) = S.mapM step $ mkStreamInner x (i,j-1) where
    step :: StreamElm x -> m (StreamElm (x:.Tbl N (UVZ.MArr0 s DIM2 e)))
    step x = let k = getTopIdx x in assert (i<=k && k<j) $ readM t (Z:.k:.j) >>= \e -> return $ SeTblNuvzMA x j e
    {-# INLINE step #-}
  mkStreamInner (x:.Tbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x +1)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Tbl N (UVZ.MArr0 s DIM2 e))))
    step (x,l)
      | l<=j      = assert (i<=k) $ readM t (Z:.k:.l) >>= \e -> return $ S.Yield (SeTblNuvzMA x l e) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}

instance (StreamElement x) => StreamElement (x:.Tbl N (UZ.MArr0 s DIM2 e)) where
  data StreamElm    (x:.Tbl N (UZ.MArr0 s DIM2 e)) = SeTblNuzMA !(StreamElm x) !Int !e
  type StreamTopIdx (x:.Tbl N (UZ.MArr0 s DIM2 e)) = Int
  type StreamArg    (x:.Tbl N (UZ.MArr0 s DIM2 e)) = StreamArg x :. e
  getTopIdx (SeTblNuzMA _ k _) = k
  getArg    (SeTblNuzMA x _ e) = getArg x :. e
  {-# INLINE getTopIdx #-}
  {-# INLINE getArg #-}

instance (Monad m, PrimMonad m, PrimState m ~ s, MkStream m x, StreamElement x, StreamTopIdx x ~ Int, Prim e) => MkStream m (x:.Tbl N (UZ.MArr0 s DIM2 e)) where
  mkStream (x:.Tbl t) (i,j) = S.mapM step $ mkStreamInner x (i,j-1) where
    step :: StreamElm x -> m (StreamElm (x:.Tbl N (UZ.MArr0 s DIM2 e)))
    step x = let k = getTopIdx x in assert (i<=k && k<j) $ readM t (Z:.k:.j) >>= \e -> e `seq` return $ SeTblNuzMA x j e
    {-# INLINE step #-}
  mkStreamInner (x:.Tbl t) (i,j) = S.flatten mk step Unknown $ mkStreamInner x (i,j-1) where
    mk :: StreamElm x -> m (StreamElm x, Int)
    mk x = return (x, getTopIdx x +1)
    step :: (StreamElm x, Int) -> m (S.Step (StreamElm x, Int) (StreamElm (x:.Tbl N (UZ.MArr0 s DIM2 e))))
    step (x,l)
      | l<=j      = assert (i<=k) $ readM t (Z:.k:.l) >>= \e -> e `seq` return $ S.Yield (SeTblNuzMA x l e) (x,l+1)
      | otherwise = return $ S.Done
      where k = getTopIdx x
    {-# INLINE mk #-}
    {-# INLINE step #-}
  {-# INLINE mkStream #-}
  {-# INLINE mkStreamInner #-}



tNtoE :: Tbl N x -> Tbl E x
tNtoE (Tbl x) = Tbl x
{-# INLINE tNtoE #-}

tEtoN :: Tbl E x -> Tbl N x
tEtoN (Tbl x) = Tbl x
{-# INLINE tEtoN #-}



-- ** Parses an empty subword. Can not be part of a more complex RHS for
-- obvious reasons: S -> E S doesn't make sense. Used in some grammars as the
-- base case.

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












-- ** Non-empty two-dimensional subwords, for non-terminal use

{-
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
    step x = let k = getTopIdx x in readM t (Z:.k:.j) >>= \e -> return $ SeNonEmptyTbl x j e
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
    step x = let k = getTopIdx x in readM t (Z:.k:.j) >>= \e -> return $ SeUVZMA x j e
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
-}

