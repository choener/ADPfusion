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



-- * Regions of unlimited size

data Region x = Region !(VU.Vector x)

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
        | otherwise = return $ S.Yield (ElmRegion s (VU.unsafeSlice k (l-k) xs) (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}

region :: VU.Vector x -> Region x
region = Region
{-# INLINE region #-}



-- * Regions of unlimited size

data SRegion x = SRegion !Int !Int !(VU.Vector x)

instance Build (SRegion x)

instance
  ( VU.Unbox x
  , StaticStack ls Subword
  ) => StaticStack (ls :!: SRegion x) Subword where
  staticStack   (ls :!: SRegion lb ub _) =
    let (a:!:Subword(i:.j):!:b) = staticStack ls
    in  (a:!:Subword(i:.j+lb):!:(max 0 $ b-lb))
  staticExtends (ls :!: SRegion lb ub xs)
    | Nothing <- se = Just $ subword 0 $ VU.length xs
    | Just sw <- se = Just sw
    where se = staticExtends ls
  {-# INLINE staticStack #-}
  {-# INLINE staticExtends #-}

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
-- TODO Need to extend (Inner Check) to (Inner Check SizeRequest); then femove filter in mkStream/Outer

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:SRegion x) Subword where
  mkStream !(ls:!:SRegion lb ub xs) Outer !ij@(Subword (i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmSRegion s (VU.unsafeSlice l (j-l) xs) (subword l j))
    $ S.filter (\s -> let (Subword (k:.l)) = getIdx s in (j-l >= lb && j-l <= ub))
    $ mkStream ls (Inner Check) ij
  mkStream !(ls:!:SRegion lb ub xs) (Inner _) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck) ij where
      mk !s = let (Subword (k:.l)) = getIdx s
              in  return (s :!: l :!: l + lb)
      step !(s :!: k :!: l)
        | l>j || l-k>ub =  return S.Done
        | otherwise     = return $ S.Yield (ElmSRegion s (VU.unsafeSlice k (l-k) xs) (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}

-- |
sregion :: Int -> Int -> VU.Vector x -> SRegion x
sregion = SRegion
{-# INLINE sregion #-}

