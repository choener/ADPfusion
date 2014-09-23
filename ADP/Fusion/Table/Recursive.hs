
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
  ) where

--import           Data.Array.Repa.Index
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size (Size(Unknown))
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.Array.Repa.Index.Subword
import           Data.PrimitiveArray ((:.)(..))

import           ADP.Fusion.Classes
import           ADP.Fusion.Table.Backtrack



data MRec m i x where
  MRec :: !(TblConstraint i) -> !(i->m x) -> MRec m i x

instance ToBT (MRec mF i x) mF mB r where
  data BT   (MRec mF i x) mF mB r = BtMRec !(TblConstraint i) (i -> mB x) (i -> mB (S.Stream mB r))
  type BtIx (MRec mF i x)         = i
  toBT (MRec c f) mrph bt = BtMRec c (mrph . f) bt
  {-# INLINE toBT #-}



-- * Instances

instance Build (MRec m i x)

-- instance Build (BtRec i f)

instance Element ls i => Element (ls :!: MRec m i x) i where
  data Elm (ls :!: MRec m i x) i = ElmMRec !x !i !(Elm ls i)
  type Arg (ls :!: MRec m i x)   = Arg ls :. x
  getArg (ElmMRec x _ ls) = getArg ls :. x
  getIdx (ElmMRec _ k _ ) = k
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: MRec m Subword x) Subword where
  mkStream (ls :!: MRec c f) Static (Subword (i:.j))
    = let ms = minSize c in ms `seq`
    S.mapM (\s -> let Subword (_:.l) = getIdx s
                    in  f (subword l j) >>= \z -> return $ ElmMRec z (subword l j) s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - ms)
  mkStream (ls :!: MRec c f) (Variable _ Nothing) (Subword (i:.j))
    = let ms = minSize c in ms `seq`
      let mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-ms)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                             y <- f (subword k (j-z))
                             return $ S.Yield (ElmMRec y (subword k $ j-z) s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

