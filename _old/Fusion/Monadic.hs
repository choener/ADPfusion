{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PackageImports #-}

-- | Monadic combinators. Code like
--
-- @f <<< xs ~~~ ys ... Stream.sum@
--
-- will generate efficient GHC core for a dynamic program comparable to
--
-- @sum [ f (xs!(i,k)) (ys!(k,j)) | k<-[i..j]]@.

module ADP.Fusion.Monadic where

import Data.Array.Repa.Index
import qualified Data.Vector.Fusion.Stream.Monadic as S

import ADP.Fusion.Monadic.Internal



-- * Apply functions to arguments.

-- | A monadic version of the function application combinator. Applies 'f'
-- which has a monadic effect.
{-
infixl 8 #<<
(#<<) f t ij = S.mapM (\(_,_,c) -> apply f c) $ streamGen t ij
{-# INLINE (#<<) #-}

-- | Pure function application combinator. Applies 'f' which is pure. The
-- arguments to 'f', meaning 't' can be monadic, however!

infixl 8 <<<
(<<<) f t ij = S.map (\(_,_,c) -> apply f c) $ streamGen t ij
{-# INLINE (<<<) #-}
-}


-- * Combine multiple right-hand sides of a non-terminal in a context-free
-- grammar.

-- | If both, 'xs' and 'ys' are streams of candidate answers, they can be
-- combined here. The answer (or sort) type of 'xs' and 'ys' has to be the
-- same. Works like @(++)@ for lists.

infixl 7 |||
(|||) xs ys ij = xs ij S.++ ys ij
{-# INLINE (|||) #-}



-- * Reduce streams to single answers.
--
-- NOTE "Single answers" can be of a vector-type! One is not constrained to
-- scalar results. This allows for many exiting algorithms.

-- | Reduces a streams of answers to the type of stored answers. The resulting
-- type could be scalar, which it will be for highest-performance algorithms,
-- or it could be a subset of answers stored in some kind of data structure.

infixl 6 ...
(...) stream h ij = h $ stream ij
{-# INLINE (...) #-}

-- | Specialized version of choice function application, with a choice function
-- that needs to know the subword index it is working on.

infixl 6 ..@
(..@) stream h ij = h ij $ stream ij
{-# INLINE (..@) #-}



-- * Combinators to chain function arguments.



-- ** General combinator creation.

-- | General function to create combinators. The left-hand side @xs@ in @xs
-- `comb` ys@ will have a size between @minL@ and @maxL@, while @ys@ and
-- /everything to its right will be guaranteed @minR@ size.

makeLeft_MinRight (minL,maxL) minR = comb where
  {-# INLINE comb #-}
  comb xs ys = Box mk step xs ys
  {-# INLINE mk #-}
  mk (z:.k:.j,a,b) = return (z:.k:.k+minL:.j,a,b)
  {-# INLINE step #-}
  step (z:.k:.l:.j,a,b)
    | l<=j-minR && l<=k+maxL = return $ S.Yield (z:.k:.l:.j,a,b) (z:.k:.l+1:.j,a,b)
    | otherwise              = return $ S.Done
{-# INLINE makeLeft_MinRight #-}

-- | Create combinators which are to be used in the right-most position of a
-- chain. 1st, they make sure that the second to last region has a size of at
-- least 'minL'. 2nd, they constrain the last argument to a size between 'minR'
-- and 'maxR'.

makeMinLeft_Right minL (minR,maxR) = comb where
  {-# INLINE comb #-}
  comb xs ys = Box mk step xs ys
  {-# INLINE mk #-}
  mk (z:.k:.j,a,b) = let l = max (k+minL) (j-maxR) in return (z:.k:.l:.j,a,b)
  {-# INLINE step #-}
  step (z:.k:.l:.j,a,b)
    | l<=j-minR = return $ S.Yield (z:.k:.l:.j,a,b) (z:.k:.l+1:.j,a,b)
    | otherwise = return $ S.Done
{-# INLINE makeMinLeft_Right #-}



-- ** A number of often-used combinators.

infixl 9 -~+, +~-, -~~, ~~-

(-~+) = makeLeft_MinRight (1,1) 1
{-# INLINE (-~+) #-}

(+~-) = makeMinLeft_Right 1 (1,1)
{-# INLINE (+~-) #-}

(-~~) = makeLeft_MinRight (1,1) 0
{-# INLINE (-~~) #-}

(~~-) = makeMinLeft_Right 0 (1,1)
{-# INLINE (~~-) #-}

(+~--) = makeMinLeft_Right 1 (2,2)
{-# INLINE (+~--) #-}

infixl 9 ~~~
(~~~) xs ys = Box mk step xs ys where
  {-# INLINE mk #-}
  mk (z:.k:.j,vidx,vstack) = return $ (z:.k:.k:.j,vidx,vstack)
  {-# INLINE step #-}
  step (z:.k:.l:.j,vidx,vstack)
    | l<=j      = return $ S.Yield (z:.k:.l:.j,vidx,vstack) (z:.k:.l+1:.j,vidx,vstack)
    | otherwise = return $ S.Done
{-# INLINE (~~~) #-}

-- | @xs +~+ ys@ with @xs@ and @ys@ non-empty. The non-emptyness constraint on
-- @ys@ works only for two arguments. With three or more arguments, a
-- left-leaning combinator to the right of @ys@ is required to establish
-- non-emptyness.

infixl 9 +~+
(+~+) xs ys = Box mk step xs ys where
  {-# INLINE mk #-}
  mk (z:.k:.j,vidx,vstack) = return $ (z:.k:.k+1:.j,vidx,vstack)
  {-# INLINE step #-}
  step (z:.k:.l:.j,vidx,vstack)
    | l+1<=j    = return $ S.Yield (z:.k:.l:.j,vidx,vstack) (z:.k:.l+1:.j,vidx,vstack)
    | otherwise = return $ S.Done
{-# INLINE (+~+) #-}

-- | @ls ~~~ xs !-~+ ys@ with xs having a size of one and @ls@ further to the
-- left having a size of one or more.

infixl 9 !-~+
(!-~+) xs ys = Box mk step xs ys where
  {-# INLINE mk #-}
  mk (z:.k:.j,vidx,vstack)
    | k>0       = return $ (z:.k:.k+1:.j,vidx,vstack)
    | otherwise = return $ (z:.k:.j+1:.j,vidx,vstack)
  {-# INLINE step #-}
  step (z:.k:.l:.j,vidx,vstack)
    | l+1<=j    = return $ S.Yield (z:.k:.l:.j,vidx,vstack) (z:.k:.j+1:.j,vidx,vstack)
    | otherwise = return $ S.Done
{-# INLINE (!-~+) #-}

-- | @xs +~-! ys ~~~ rs@ with @ys@ having a size of one and @rs@ further to the
-- right having a size of one.

infixl 9 +~-!
(+~-!) xs ys = Box mk step xs ys where
  {-# INLINE mk #-}
  mk (z:.k:.j,vidx,vstack) = return $ (z:.k:.j-2:.j,vidx,vstack)
  {-# INLINE step #-}
  step (z:.k:.l:.j,vidx,vstack)
    | l+2==j    = return $ S.Yield (z:.k:.l:.j,vidx,vstack) (z:.k:.j+1:.j,vidx,vstack)
    | otherwise = return $ S.Done
{-# INLINE (+~-!) #-}

-- | @xs -~- ys@ produces an answer only if both @xs@ and @ys@ have size one.
-- The total size here then is two.

infixl 9 -~-
(-~-) xs ys = Box mk step xs ys where
  {-# INLINE mk #-}
  mk (z:.k:.j,vidx,vstack) = return $ (z:.k:.k+1:.j,vidx,vstack)
  {-# INLINE step #-}
  step (z:.k:.l:.j,vidx,vstack)
    | k+1==l && l+1==j = return $ S.Yield (z:.k:.l:.j,vidx,vstack) (z:.k:.l+1:.j,vidx,vstack)
    | otherwise        = return $ S.Done
{-# INLINE (-~-) #-}

