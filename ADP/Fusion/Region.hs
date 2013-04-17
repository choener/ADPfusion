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



data Region x = Region !(VU.Vector x)
--              | SRegion !Int !Int !(VU.Vector x)

instance Build (Region x)

instance
  ( VU.Unbox x
  , StaticStack ls Subword
  ) => StaticStack (ls :!: Region x) Subword where
  staticStack   (ls :!: _) = staticStack ls
  staticExtends (ls :!: Region xs)
    | Nothing <- se = Just $ subword 0 $ VU.length xs
    | Just sw <- se = Just sw
    where se = staticExtends ls
  {-# INLINE staticStack #-}
  {-# INLINE staticExtends #-}

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
    $ mkStream ls (Inner Check) ij
  mkStream !(ls:!:Region xs) (Inner _) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck) ij where
      mk !s = let (Subword (k:.l)) = getIdx s
              in  return (s :!: l :!: l)
      step !(s :!: k :!: l)
        | l > j     =  return S.Done
        | otherwise = return $ S.Yield (ElmRegion s (VU.unsafeSlice k (l-k) xs) (subword k l)) (s :!: k :!: l+1) -- TODO the slice index positions are wrong ?!
  --
  -- Regions with size limitations
  --
  -- TODO this case seems to be rather inefficient. We should rather not do the
  -- takeWhile/dropWhile dance modify the inner index to produce only those
  -- values that are acceptable
--  mkStream !(ls:!:Region lb ub xs) Outer !ij@(Subword (i:.j))
--    = S.map       (\s -> let (Subword (k:.l)) = getIdx s in ElmRegion s (VU.unsafeSlice l (j-l) xs) (subword l j))
--    $ S.takeWhile (\s -> case mlb of Nothing -> True
--                                     Just lb -> let (Subword (k:.l)) = getIdx s in j-l >= lb)
--    $ S.dropWhile (\s -> case mub of Nothing -> False
--                                     Just ub -> let (Subword (k:.l)) = getIdx s in j-l >= ub)
--    $ mkStream ls Inner ij
{-
  -- | TODO below is wrong for sregions!
  mkStream !(ls:!:SRegion lb ub xs) Outer !ij@(Subword (i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmRegion s (VU.slice l (j-l) xs) (subword l j))
    $ mkStream ls (Inner Check) ij
  mkStream !(ls:!:SRegion lb ub xs) (Inner _) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck) ij where
      mk !s = let (Subword (k:.l)) = getIdx s
              in  return (s :!: l :!: l+lb)
      step !(s :!: k :!: l) | l > j || l-k > ub
        = return S.Done
      step !(s :!: k :!: l)
        = return $ S.Yield (ElmRegion s (VU.unsafeSlice k (l-k) xs) (subword k l)) (s :!: k :!: l+1) -- TODO the slice index positions are wrong ?!
-}
  {-# INLINE mkStream #-}

region :: VU.Vector x -> Region x
region = Region
{-# INLINE region #-}

-- |
--
-- NOTE If you only want a lower bound, set the upper bound to s.th. like "1
-- Million".

--sregion :: Int -> Int -> VU.Vector x -> Region x
--sregion = SRegion
--{-# INLINE sregion #-}

