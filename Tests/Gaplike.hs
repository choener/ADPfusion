{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | The palindrome mini-example showing how to use the new GAPlike-version of
-- ADP together with algebra products. Given nested paired equal characters,
-- counts the number of pairs.
--
-- Especially the backtracking is full of nested monads. While mostly useless
-- here (backtracking is done in the Identity monad), this would allow
-- stochastic backtracking to fire, or another scheme, while backtracking.
--
-- This problem does /not/ need a dynamic program to solve it. We are actually
-- slower than other solutions. This test program is only here to show how to
-- write the forward and backward/backtracking steps.
--
-- TODO Though in that case, it could be useful, to parametrize over two
-- different monads (transformer stacks)...

module Tests.Gaplike where

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Primitive
import Data.Vector.Fusion.Stream.Monadic as SM
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util
import Prelude as P
import "PrimitiveArray" Data.Array.Repa.Index
import qualified Data.Vector.Unboxed as VU

import Data.PrimitiveArray as PA hiding (E)
import qualified Data.PrimitiveArray.Zero as Z

import ADP.Fusion.GAPlike

import Debug.Trace



-- | Signature: we have three functions: (i) the empty case "() -> x", (ii)
-- extension of the palindrome by paired characters, (iii) and the objective
-- function returning an answer in the current monad.

type Signature m x y =
  ( () -> x
  , Char -> x -> Char -> x
  , Char -> Char -> x
  , x -> x -> x
  , SM.Stream m x -> m y
  )

-- | Very simple grammar. Either we parse the empty string, or extend the
-- current string with a character to the left and to the right. There is only
-- one non-terminal: "tbl".

gSimple (empty,pair,chrchr,tbltbl,h) tbl c e = 
  (tbl,
        empty <<< e           |||
        chrchr <<< c % c      |||
--        (\ij -> SM.map (\s -> apply chrchr $ getArg s) $ mkStream (None:.c:.c) ij) ... h
        pair  <<< c % tbl % c |||
        tbltbl <<< tbl % tbl ... h
  )
{-# INLINE gSimple #-}

-- | Simple scoring system. The empty string has a score of "0", a palindrome
-- gets a score of +1 to the inner part. If we are not palindromic, the total
-- score is reset to "-999999".

aMax :: Monad m => Signature m Int Int
aMax = (empty,pair,chrchr,tbltbl,h) where
  empty _ = 0
  {-# INLINE empty #-}
  pair l x r = if l==r then x+1 else -999999
  {-# INLINE pair #-}
  chrchr (!l) (!r) = if l==r then 2 else -999999
  {-# INLINE chrchr #-}
  tbltbl (!l) (!r) = l+r
  {-# INLINE tbltbl #-}
  h = SM.foldl' max (-999999)
  {-# INLINE h #-}
{-# INLINE aMax #-}

-- | Pretty Printer. Will print nested angled brackets for a palindrome.

aPretty = (empty,pair,chrchr,tbltbl,h) where
  empty _ = ""
  pair l x r = if l==r then "<" P.++ x P.++ ">" else "." P.++ x P.++ "."
  chrchr l r = if l==r then "<>" else ".."
  tbltbl l r = l P.++ r
  h = return . id
{-# INLINE aPretty #-}

-- | Run the palindrome dynamic program, giving the number of pairs, and the
-- nested brackets.

palindrome inp = (arr ! (Z:.0:.n), bt) where
  (_,Z:._:.n) = bounds arr
  len = P.length inp
  !arr = runST (fillPalindrome vinp)
  vinp = VU.fromList $ inp
  bt = backtrack vinp arr
{-# NOINLINE palindrome #-}

-- | Fills the DP table. We create a primitive array, bind it to the table
-- constructor ('Tbl' is part of "ADP.Fusion.Gaplike"). Then we bind the input
-- to 'Chr', and finally the 'Empty' terminal to have a base case.
--
-- Now, we just need to fill the table using the 'fillTable' function. (Which
-- needs to go into a library soon).
--
-- NOTE we don't inline this thing, mostly because this wouldn't yield any
-- performance improvements. Also, it is nice to be able to look at the core of
-- "fillPalindrome".

fillPalindrome :: forall s . VU.Vector Char -> ST s (Z.U DIM2 Int)
fillPalindrome inp = do
  let n = VU.length inp
  t' <- fromAssocsM (Z:.0:.0) (Z:.n:.n) (-999999) []
  let t = mtblE t'
      {-# INLINE t #-}
  let c = Chr inp
      {-# INLINE c #-}
  let e = Empty
      {-# INLINE e #-}
  fillTable $ gSimple aMax t c e
  PA.freeze t'
{-# NOINLINE fillPalindrome #-}

-- | Fill a dynamic programming table "tbl" using the function "f". This will
-- actually be a library function soon, but just for /educational/ purposes, we
-- show it here.
--
-- TODO We actually need to make a small library of fillXYZ functions.

fillTable :: PrimMonad m => (MTbl E (Z.MU m DIM2 Int), ((Int,Int) -> m Int)) -> m ()
fillTable  (MTbl tbl, f) = do
  let (_,Z:.n:._) = boundsM tbl
  forM_ [n,n-1..0] $ \i -> forM_ [i..n] $ \j -> do
    v <- f (i,j)
    v `seq` writeM tbl (Z:.i:.j) v
{-# INLINE fillTable #-}

-- | Backtracking works like the forward phase. We bind our input and table.
-- But now, instead of filling a table, we call the grammar function with the
-- outermost indices (could be hidden in what ADP calls the "axiom") and remove
-- all the monadic stuff.
--
-- While this looks a bit superfluous, it allows us to have effects in
-- backtracking, that would otherwise not be possible. And we can /combine/
-- functions.

backtrack (inp :: VU.Vector Char) (tbl :: Z.U DIM2 Int) = unId . SM.toList . unId $ g (0,n) where
  n = VU.length inp
  c = Chr inp
  e = Empty
  t = bttblE tbl (g :: BTfun Id String)
  (_,g) = gSimple (aMax <** aPretty) t c e
{-# INLINE backtrack #-}

-- | The signature, given two algebras. The first algebra should normally be
-- the same one used to fill the table (or some stochastic version of it),
-- while the second should produce some result, say a prettry-printed
-- backtrack.
--
-- TODO generalize the 'hfs' part: we need a type class, or s.th. as we either
-- need (==) or elem depending on 'f'

type CombSignature m e b =
  ( () -> (e, m (SM.Stream m b))
  , Char -> (e, m (SM.Stream m b)) -> Char -> (e, m (SM.Stream m b))
  , Char -> Char -> (e, m (SM.Stream m b))
  , (e,m (SM.Stream m b)) -> (e, m (SM.Stream m b)) -> (e, m (SM.Stream m b))
  , SM.Stream m (e, m (SM.Stream m b)) -> m (SM.Stream m b)
  )

-- | The algebra product. Combination of scoring functions is more complicated
-- as the second algebra get mangled into the stream stuff. The objective
-- function is quite harmless. Select the single optimal entry using the first
-- function. Filter everything based on this result. Then concatenate the
-- results of the second function, finally applying the objective function for
-- those things. And done.

instance Show (Id [String]) where
  show xs = show $ unId xs

(<**)
  :: (Monad m, Eq b, Eq e, Show b, Show e, Show (m [b]))
  => Signature m e e
  -> Signature m b (SM.Stream m b)
  -> CombSignature m e b
(<**) f s = (empty,pair,chrchr,tbltbl,h) where
  (emptyF,pairF,chrchrF,tbltblF,hF) = f
  (emptyS,pairS,chrchrS,tbltblS,hS) = s

  empty e = let x = (emptyF e, return $ SM.singleton (emptyS e)) in x
  pair l (x,ys) r = (pairF l x r, ys >>= \ys' -> return $ SM.map (\y -> pairS l y r) ys')
  chrchr l r = (chrchrF l r, return $ SM.singleton (chrchrS l r))
  tbltbl (x,xs) (y,ys) = (tbltblF x y, error "tbltbl missing")
  h xs = do
    hfs <- hF $ SM.map fst xs
    let phfs = SM.concatMapM snd . SM.filter ((hfs==) . fst) $ xs
    hS phfs

