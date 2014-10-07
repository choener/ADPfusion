
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Bind a non-terminal to a non-memoizing, and hence recursive, table.

module ADP.Fusion.Table.Recursive
  ( IRec (..)
  ) where

--import           Data.Array.Repa.Index
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size (Size(Unknown))
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.Array.Repa.Index.Subword
import           Data.PrimitiveArray ((:.)(..))

import           ADP.Fusion.Classes
import           ADP.Fusion.Table.Backtrack



data IRec m i x where
  IRec :: !(TblConstraint i) -> (i,i) -> !(i->m x) -> IRec m i x

instance ToBT (IRec mF i x) mF mB r where
  data BT   (IRec mF i x) mF mB r = BtIRec !(TblConstraint i) (i,i) (i -> mB x) (i -> mB (S.Stream mB r))
  type BtIx (IRec mF i x)         = i
  toBT (IRec c i f) mrph bt = BtIRec c i (mrph . f) bt
  {-# INLINE toBT #-}



-- * Instances

instance Build (IRec m i x)

instance Element ls i => Element (ls :!: IRec m i x) i where
  data Elm (ls :!: IRec m i x) i = ElmIRec !x !i !(Elm ls i)
  type Arg (ls :!: IRec m i x)   = Arg ls :. x
  getArg (ElmIRec x _ ls) = getArg ls :. x
  getIdx (ElmIRec _ k _ ) = k
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance Element ls i => Element (ls :!: (BT (IRec mF i x) mF mB r)) i where
  data Elm (ls :!: (BT (IRec mF i x) mF mB r)) i = ElmBtIRec !x !(mB (S.Stream mB r)) !i !(Elm ls i)
  type Arg (ls :!: (BT (IRec mF i x) mF mB r))   = Arg ls :. (x, mB (S.Stream mB r))
  getArg (ElmBtIRec x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtIRec _ _ i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance ModifyConstraint (IRec m Subword x) where
  toNonEmpty (IRec _ i f) = IRec NonEmpty i f
  toEmpty    (IRec _ i f) = IRec EmptyOk  i f
  {-# INLINE toNonEmpty #-}
  {-# INLINE toEmpty    #-}

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: IRec m Subword x) Subword where
  mkStream (ls :!: IRec c _ f) Static (Subword (i:.j))
    = let ms = minSize c in ms `seq`
    S.mapM (\s -> let Subword (_:.l) = getIdx s
                    in  f (subword l j) >>= \z -> return $ ElmIRec z (subword l j) s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - ms)
  mkStream (ls :!: IRec c _ f) (Variable _ Nothing) (Subword (i:.j))
    = let ms = minSize c in ms `seq`
      let mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-ms)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                             y <- f (subword k (j-z))
                             return $ S.Yield (ElmIRec y (subword k $ j-z) s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

instance
  ( Monad mB
  , Element ls Subword
  , MkStream mB ls Subword
  ) => MkStream mB (ls :!: BT (IRec mF Subword x) mF mB r) Subword where
  mkStream (ls :!: BtIRec c _ f bt) Static (Subword (i:.j))
    = let ms = minSize c in ms `seq`
      S.mapM (\s -> let (Subword (_:.l)) = getIdx s
                        ix               = subword l j
                    in  f ix >>= \fx -> return $ ElmBtIRec fx (bt ix) ix s)
      $ mkStream ls (Variable Check Nothing) (subword i $ j-ms)
  mkStream (ls :!: BtIRec c _ f bt) (Variable _ Nothing) (Subword (i:.j))
    = let ms = minSize c
          mk s = let Subword (_:.l) = getIdx s in return (s:.j-l-ms)
          step (s:.z)
            | z>=0      = do let Subword (_:.k) = getIdx s
                                 ix             = subword k (j-z)
                             f ix >>= \fx -> return $ S.Yield (ElmBtIRec fx (bt ix) ix s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in ms `seq` S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

