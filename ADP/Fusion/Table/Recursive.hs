
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Bind a non-terminal to a non-memoizing, and hence recursive, table.

module ADP.Fusion.Table.Recursive
  ( MRec (..)
  , MRecTy
  , BtRec (..)
  , BtRecTy
  ) where

import           Data.Array.Repa.Index
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size (Size(Unknown))
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.Array.Repa.Index.Subword

import           ADP.Fusion.Classes



data MRec i f where
  MRec :: (f ~ (i -> m x)) => !(TblConstraint i) -> !(i->m x) -> MRec i f

type MRecTy i f = MRec i f -- f ~ i -> m x

data BtRec i f = BtRec !(TblConstraint i) !f

type BtRecTy m i x r = BtRec i (i -> m (S.Stream m r))



-- * Instances

instance Build (MRec i f)

instance Build (BtRec i f)

instance Element ls i => Element (ls :!: MRecTy i (i->m x)) i where
  data Elm (ls :!: MRecTy i (i->m x)) i = ElmMRec !x !i !(Elm ls i)
  type Arg (ls :!: MRecTy i (i->m x))   = Arg ls :. x
  getArg (ElmMRec x _ ls) = getArg ls :. x
  getIdx (ElmMRec _ k _ ) = k
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: MRecTy Subword (Subword -> m x)) Subword where
  mkStream (ls :!: MRec c f) Static (Subword (i:.j))
    = S.mapM (\s -> let Subword (_:.l) = getIdx s
                    in  f (subword l j) >>= \z -> return $ ElmMRec z (subword l j) s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - minSize c)
  mkStream (ls :!: MRec c f) (Variable _ Nothing) (Subword (i:.j))
    = let mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-minSize c)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                             y <- f (subword k (j-z))
                             return $ S.Yield (ElmMRec y (subword k $ j-z) s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

