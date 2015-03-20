
module ADP.Fusion.Table.Array.Subword where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Data.Vector.Fusion.Stream.Monadic
import Debug.Trace
import Prelude hiding (map)

import           Data.PrimitiveArray hiding (map)

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
    = map (\s -> let (Subword (_:.l)) = getIdx s
                 in  ElmITbl (t ! subword l j) (subword l j) (subword 0 0) s)
    $ mkStream ls IVariable hh (delay_inline Subword (i:.j - minSize c))
  mkStream (ls :!: ITbl c t _) IVariable hh (Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls IVariable hh (delay_inline Subword (i:.j - minSize c))
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ Yield (ElmITbl (t ! kl) kl (subword 0 0) s) (s:. z-1)
                      | otherwise = return $ Done
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
    = map (\s -> let Subword (_:.l) = getIdx s
                     lj             = subword l j
                 in  ElmBtITbl (t ! lj) (bt hh lj) lj (subword 0 0) s)
    $ mkStream ls IVariable hh (delay_inline subword i $ j - minSize c)
  mkStream (ls :!: BtITbl c t bt) IVariable hh ij@(Subword (i:.j))
    = flatten mk step Unknown $ mkStream ls IVariable hh (delay_inline subword i j)
    where mk s = let Subword (_:.l) = getIdx s in return (s :. j - l - minSize c)
          step (s:.z) | z >= 0 = do let Subword (_:.k) = getIdx s
                                        l              = j - z
                                        kl             = subword k l
                                    return $ Yield (ElmBtITbl (t ! kl) (bt hh kl) kl (subword 0 0) s) (s:.z-1)
                      | otherwise = return $ Done
  {-# Inline mkStream #-}


instance
  ( Monad m
  , Element ls (Outside Subword)
  , PrimArrayOps arr (Outside Subword) x
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: ITbl m arr (Outside Subword) x) (Outside Subword) where
  -- TODO what about @c / minSize@
  mkStream (ls :!: ITbl c t _) (OStatic d) u ij@(O (Subword (i:.j)))
    = map (\s -> let O (Subword (k:._)) = getOmx s
                     kj = O $ Subword (k:.j)
                 in  ElmITbl (t ! kj) ij kj s) -- @ij@ or s.th. else shouldn't matter?
    $ mkStream ls (OFirstLeft d) u ij
  mkStream (ls :!: ITbl c t _) (ORightOf d) u@(O (Subword (_:.h))) ij@(O (Subword (i:.j)))
    = flatten mk step Unknown $ mkStream ls (OFirstLeft d) u ij
      where mk s = return (s:.j)
            step (s:.l) | l <= h = do let (O (Subword (k:._))) = getIdx s
                                          kl = O $ Subword (k:.l)
                                      return $ Yield (ElmITbl (t ! kl) (O (Subword (j:.j))) kl s) (s:.l+1)
                        | otherwise = return $ Done
            {-# Inline [0] mk   #-}
            {-# Inline [0] step #-}
  mkStream (ls :!: ITbl c t _) (OFirstLeft d) u ij = error "Array/Outside Subword : OFirstLeft : should never be reached!"
  mkStream (ls :!: ITbl c t _) (OLeftOf d) u ij = error "Array/Outside Subword : OLeftOf : should never be reached!"
  {-# Inline mkStream #-}



instance
  ( Monad m
  , Element ls (Outside Subword)
  , PrimArrayOps arr Subword x
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: ITbl m arr Subword x) (Outside Subword) where
  -- TODO what about @c / minSize@
  mkStream (ls :!: ITbl c t _) (OStatic d) u ij@(O (Subword (i:.j)))
    = map (\s -> let O (Subword (_:.k))     = getIdx s
                     o@(O (Subword (_:.l))) = getOmx s
                     kl = Subword (k:.l)
                 in ElmITbl (t ! kl) (O kl) o s)
    $ mkStream ls (ORightOf d) u ij
  mkStream (ls :!: ITbl c t _) (ORightOf d) u@(O (Subword (_:.h))) ij@(O (Subword (i:.j)))
    = flatten mk step Unknown $ mkStream ls (ORightOf d) u ij
    where mk s = let O (Subword (_:.l)) = getIdx s
                 in  return (s :.l:.l + minSize c)
          step (s:.k:.l)
            | let O (Subword (_:.o)) = getOmx s
            , l <= o = do let kl = Subword (k:.l)
                          return $ Yield (ElmITbl (t ! kl) (O kl) (getOmx s) s) (s:.k:.l+1)
            | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  mkStream (ls :!: ITbl c t _) (OFirstLeft d) u ij@(O (Subword (i:.j)))
    = map (\s -> let O (Subword (l:._)) = getOmx s
                     O (Subword (_:.k)) = getIdx s
                     kl = Subword (k:.i)
                 in  ElmITbl (t ! kl) (O kl) (getOmx s) s)
    $ mkStream ls (OLeftOf d) u ij
  mkStream (ls :!: ITbl c t _) (OLeftOf d) u ij@(O (Subword (i:.j)))
    = flatten mk step Unknown $ mkStream ls (OLeftOf d) u ij
    where mk s = let O (Subword (_:.l)) = getIdx s in return (s:.l)
          step (s:.l) | l <= i = do let O (Subword (_:.k)) = getIdx s
                                        kl = Subword (k:.l)
                                    return $ Yield (ElmITbl (t ! kl) (O kl) (getOmx s) s) (s:.l+1)
                      | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}



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

