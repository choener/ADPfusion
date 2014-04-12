{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module ADP.Fusion.Region where

import           Data.Array.Repa.Index
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU

import           Data.Array.Repa.Index.Subword

import           ADP.Fusion.Classes



-- | Regions allow terminal parsers that return 0 to many characters as a slice
-- of a vector.

data (VG.Vector v x) => Region v x = Region !(v x)

region :: VG.Vector v x => v x -> Region v x
region = Region
{-# INLINE region #-}

instance Build (Region v x)

instance
  ( Element ls Subword
  ) => Element (ls :!: Region v x) Subword where
    data Elm (ls :!: Region v x) Subword = ElmRegion !(v x) !Subword !(Elm ls Subword)
    type Arg (ls :!: Region v x) = Arg ls :. v x
    getArg (ElmRegion vx _ ls) = getArg ls :. vx
    getIdx (ElmRegion _  i _ ) = i
    {-# INLINE getArg #-}
    {-# INLINE getIdx #-}

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  , VG.Vector v x
  ) => MkStream m (ls :!: Region v x) Subword where
  mkStream (ls :!: Region xs) Static ij@(Subword (i:.j))
    = S.map (\s -> let Subword (k:.l) = getIdx s
                   in  ElmRegion (VG.unsafeSlice l (j-k-1) xs) (subword l j) s
            )
    $ mkStream ls (Variable Check Nothing) (subword i j)
  mkStream (ls :!: Region xs) (Variable _ Nothing) (Subword (i:.j))
    = let mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                             let y = VG.unsafeSlice k z xs
                             return $ S.Yield (ElmRegion y (subword k $ j-z) s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in  S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}


