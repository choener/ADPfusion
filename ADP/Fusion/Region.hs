{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module ADP.Fusion.Region where

import Data.Array.Repa.Index
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Data.Strict.Maybe
import Prelude hiding (Maybe(..))

import Data.Array.Repa.Index.Subword

import ADP.Fusion.Classes

import Control.Exception (assert)
import Debug.Trace



-- * Regions of unlimited size

data Region x = Region !(VU.Vector x)

instance Build (Region x)

instance
  ( ValidIndex ls Subword
  , VU.Unbox xs
  ) => ValidIndex (ls :!: Region xs) Subword where
  validIndex (ls :!: Region xs) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
    i>=a && j<=VU.length xs -c && i+b<=j && validIndex ls abc ij
  {-# INLINE validIndex #-}
  getParserRange (ls :!: Region xs) ix = let (a:!:b:!:c) = getParserRange ls ix in (a:!:b:!:c)
  {-# INLINE getParserRange #-}

instance
  ( Elms ls Subword
  ) => Elms (ls :!: Region x) Subword where
  data Elm (ls :!: Region x) Subword = ElmRegion !(Elm ls Subword) !(VU.Vector x) !Subword
  type Arg (ls :!: Region x)         = Arg ls :. VU.Vector x
  getArg !(ElmRegion ls xs _) = getArg ls :. xs
  getIdx !(ElmRegion _ _   i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:Region x) Subword where
  mkStream !(ls:!:Region xs) Outer !ij@(Subword (i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmRegion s (VU.unsafeSlice l (j-l) xs) (subword l j))
    $ mkStream ls (Inner Check Nothing) ij
  mkStream !(ls:!:Region xs) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
      mk !s = let (Subword (k:.l)) = getIdx s
                  l' = case szd of Nothing -> l
                                   Just z  -> max l (j-z)
              in  return (s :!: l :!: l')
      step !(s :!: k :!: l)
        | l > j     =  return S.Done
        | otherwise = return $ S.Yield (ElmRegion s (VU.unsafeSlice k (l-k) xs) (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}

region :: VU.Vector x -> Region x
region = Region
{-# INLINE region #-}



-- * Regions of unlimited size

data SRegion x = SRegion !Int !Int !(VU.Vector x)

instance Build (SRegion x)

instance
  ( ValidIndex ls Subword
  , VU.Unbox xs
  ) => ValidIndex (ls :!: SRegion xs) Subword where
  validIndex (ls :!: SRegion lb ub xs) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
    i>=a && j<=VU.length xs -c && i+b<=j && validIndex ls abc ij
  {-# INLINE validIndex #-}
  getParserRange (ls :!: SRegion lb ub xs) ix = let (a:!:b:!:c) = getParserRange ls ix in (a:!:b+lb:!:max 0 (c-lb))
  {-# INLINE getParserRange #-}

instance
  ( Elms ls Subword
  ) => Elms (ls :!: SRegion x) Subword where
  data Elm (ls :!: SRegion x) Subword = ElmSRegion !(Elm ls Subword) !(VU.Vector x) !Subword
  type Arg (ls :!: SRegion x)         = Arg ls :. VU.Vector x
  getArg !(ElmSRegion ls xs _) = getArg ls :. xs
  getIdx !(ElmSRegion _ _   i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

-- |
--
-- TODO Check that all inner / outer sized calculations are correct
--
-- NOTE mkStream/Inner gives a size hint of Nothing, as in purely inner cases,
-- min/max boundaries are determined solely from the running rightmost index
-- from the next inner component.
--
-- NOTE the filter in mkStream/Outer is still necessary to check for
-- lowerbound>0 conditions. We /could/ send the lower bound down with another
-- size hint, but this only makes sense if you have use cases, where the lower
-- bound is a lot higher than "0". Otherwise the current code is simpler.
--
-- TODO use drop instead of filter: still condition, but large lower bounds are captured
--
-- TODO remove mkStream/Outer : filter and test if one condition less gives
-- much better runtimes.

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:SRegion x) Subword where
  mkStream !(ls:!:SRegion lb ub xs) Outer !ij@(Subword (i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s in assert (l>=0 && j-i>=0) $ ElmSRegion s (VU.slice l (j-l) xs) (subword l j))
    $ S.filter (\s -> let (Subword (k:.l)) = getIdx s in (j-l >= lb && j-l <= ub))
    $ mkStream ls (Inner Check (Just ub)) ij
  mkStream !(ls:!:SRegion lb ub xs) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
      mk !s = let (Subword (k:.l)) = getIdx s
                  l' = case szd of Nothing -> l+lb
                                   Just z  -> max (l+lb) (j-z)
              in  return (s :!: l :!: l')
      step !(s :!: k :!: l)
        | l>j || l-k>ub =  return S.Done
        | otherwise     = return $ assert (k>=0 && l-k>=0) $ S.Yield (ElmSRegion s (VU.slice k (l-k) xs) (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}

-- |
sregion :: Int -> Int -> VU.Vector x -> SRegion x
sregion = SRegion
{-# INLINE sregion #-}

