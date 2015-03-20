
module ADP.Fusion.Table.Array.Subword where

import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size
import           Data.Vector.Fusion.Util (delay_inline)
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           Debug.Trace

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Table.Array.Type
import           ADP.Fusion.Table.Backtrack




-- TODO delay inline @(subword i $ j - minSize c)@ or face fusion-breakage.
-- Can we just have @Inline [0] subword@ to fix this?

instance
  ( Monad m
  , Element ls Subword
  , PrimArrayOps arr Subword x
  , MkStream m ls Subword
  ) => MkStream m (ls :!: ITbl m arr Subword x) Subword where
  mkStream (ls :!: ITbl c t _) IStatic hh (Subword (i:.j))
    = S.map (\s -> let (Subword (_:.l)) = getIdx s
                   in  ElmITbl (t ! subword l j) (subword l j) (subword 0 0) s)
    $ mkStream ls IVariable hh (delay_inline Subword (i:.j - minSize c))
  mkStream (ls :!: ITbl c t _) IVariable hh (Subword (i:.j))
    = S.flatten mk step Unknown $ mkStream ls IVariable hh (delay_inline Subword (i:.j - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ S.Yield (ElmITbl (t ! kl) kl (subword 0 0) s) (s:.z-1)
                      | otherwise = return $ S.Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls Subword
  , MkStream mB ls Subword
  , PrimArrayOps arr Subword x
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr Subword x) mF mB r) Subword where
  mkStream (ls :!: BtITbl c t bt) IStatic hh ij@(Subword (i:.j))
    = S.map (\s -> let Subword (_:.l) = getIdx s
                       lj             = subword l j
                   in  ElmBtITbl (t ! lj) (bt hh lj) lj (subword 0 0) s)
    $ mkStream ls IVariable hh (delay_inline Subword (i:.j - minSize c))
  mkStream (ls :!: BtITbl c t bt) IVariable hh ij@(Subword (i:.j))
    = S.flatten mk step Unknown $ mkStream ls IVariable hh (delay_inline Subword (i:.j - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ S.Yield (ElmBtITbl (t ! kl) (bt hh kl) kl (subword 0 0) s) (s:.z-1)
                      | otherwise = return $ S.Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}


instance
  ( Monad m
  , Element ls (Outside Subword)
  , PrimArrayOps arr (Outside Subword) x
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: ITbl m arr (Outside Subword) x) (Outside Subword) where



instance
  ( Monad m
  , Element ls (Outside Subword)
  , PrimArrayOps arr Subword x
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: ITbl m arr Subword x) (Outside Subword) where



instance ModifyConstraint (ITbl m arr Subword x) where
  toNonEmpty (ITbl _ arr f) = ITbl NonEmpty arr f
  toEmpty    (ITbl _ arr f) = ITbl EmptyOk  arr f
  {-# Inline toNonEmpty #-}
  {-# Inline toEmpty #-}

instance ModifyConstraint (Backtrack (ITbl mF arr Subword x) mF mB r) where
  toNonEmpty (BtITbl _ arr bt) = BtITbl NonEmpty arr bt
  toEmpty    (BtITbl _ arr bt) = BtITbl EmptyOk  arr bt
  {-# Inline toNonEmpty #-}
  {-# Inline toEmpty #-}

