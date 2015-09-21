
module ADP.Fusion.SynVar.Array
  ( module ADP.Fusion.SynVar.Array.Type
--  , module ADP.Fusion.SynVar.Array.Point
--  , module ADP.Fusion.SynVar.Array.Set
--  , module ADP.Fusion.SynVar.Array.Subword
  ) where


import Data.Proxy
import Data.Strict.Tuple hiding (snd)
import Prelude hiding (map,mapM)
import Data.Vector.Fusion.Stream.Monadic

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices
import ADP.Fusion.SynVar.Backtrack

--import ADP.Fusion.SynVar.Array.Point
--import ADP.Fusion.SynVar.Array.Set
--import ADP.Fusion.SynVar.Array.Subword
import ADP.Fusion.SynVar.Array.TermSymbol
import ADP.Fusion.SynVar.Array.Type




instance
  ( Monad m
  , Element ls (i I)
  , PrimArrayOps arr u x
  , TblConstraint u ~ TableConstraint
  , AddIndexDense (Z:.i I) (Z:.u) (Z:.i I)
  , TableStaticVar u (i I)
  , MkStream m ls (i I)
  ) => MkStream m (ls :!: ITbl m arr u x) (i I) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (i I)
  , MkStream mB ls (i I)
  , TblConstraint u ~ TableConstraint
  , AddIndexDense (Z:.i I) (Z:.u) (Z:.i I)
  , TableStaticVar u (i I)
  , PrimArrayOps arr u x
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr u x) mF mB r) (i I) where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = mapM (\(s,ii,oo,ii',oo') -> bt us' ii >>= \ ~bb -> return $ ElmBtITbl (t!ii) bb ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
    where !us' = snd $ bounds t
  {-# Inline mkStream #-}

-- | An outside table in an outside index context.
--
-- TODO what about @c / minSize@

instance
  ( Monad m
  , Element ls (i O)
  , PrimArrayOps arr (u O) x
  , TblConstraint (u O) ~ TableConstraint
  , AddIndexDense (Z:.i O) (Z:.u O) (Z:.i O)
  , TableStaticVar (u O) (i O)
  , MkStream m ls (i O)
  ) => MkStream m (ls :!: ITbl m arr (u O) x) (i O) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!oo) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (u O)) c vs is) us (tableStreamIndex (Proxy :: Proxy (u O)) c vs is)
  {-# Inline mkStream #-}

-- | An inside table in an outside index context.

instance
  ( Monad m
  , Element ls (i O)
  , PrimArrayOps arr (u I) x
  , TblConstraint (u I) ~ TableConstraint
  , AddIndexDense (Z:.i O) (Z:.u I) (Z:.i O)
  , TableStaticVar (u I) (i O)
  , MkStream m ls (i O)
  ) => MkStream m (ls :!: ITbl m arr (u I) x) (i O) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (u I)) c vs is) us (tableStreamIndex (Proxy :: Proxy (u I)) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (i C)
  , PrimArrayOps arr (u I) x
  , MkStream m ls (i C)
  , TblConstraint (u I) ~ TableConstraint
  , AddIndexDense (Z:.i C) (Z:.u I) (Z:.i C)
  , TableStaticVar (u I) (i C)
  ) => MkStream m (ls :!: ITbl m arr (u I) x) (i C) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (u I)) c vs is) us (tableStreamIndex (Proxy :: Proxy (u I)) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (i C)
  , PrimArrayOps arr (u O) x
  , MkStream m ls (i C)
  , TblConstraint (u O) ~ TableConstraint
  , AddIndexDense (Z:.i C) (Z:.u O) (Z:.i C)
  , TableStaticVar (u O) (i C)
  ) => MkStream m (ls :!: ITbl m arr (u O) x) (i C) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!oo) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (u O)) c vs is) us (tableStreamIndex (Proxy :: Proxy (u O)) c vs is)
  {-# Inline mkStream #-}



instance ModifyConstraint (ITbl m arr (Subword t) x) where
  toNonEmpty (ITbl b l _ arr f) = ITbl b l NonEmpty arr f
  toEmpty    (ITbl b l _ arr f) = ITbl b l EmptyOk  arr f
  {-# Inline toNonEmpty #-}
  {-# Inline toEmpty #-}

instance ModifyConstraint (Backtrack (ITbl mF arr (Subword t) x) mF mB r) where
  toNonEmpty (BtITbl _ arr bt) = BtITbl NonEmpty arr bt
  toEmpty    (BtITbl _ arr bt) = BtITbl EmptyOk  arr bt
  {-# Inline toNonEmpty #-}
  {-# Inline toEmpty #-}




class Boo x where
  foo :: x -> String

instance (Show (i I)) => Boo (i I) where
  foo s = "dat " Prelude.++ show s

instance (Show (i I), Show ts) => Boo (i I :> ts) where
  foo s = show s

data Xi i t = Xi
  deriving (Show)

--instance Show (x i I) => Boo (x i I) where
--  foo s = show s

data Bs2i t where
  Bs2i :: Interface i -> Interface j -> Bs2i t

instance Show (Bs2i t) where
  show _ = "x"




{-

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}

-- | Tables in ADPfusion memoize results of parses. In the forward phase, table
-- cells are filled by a table-filling method from @Data.PrimitiveArray@. In
-- the backtracking phase, grammar rules are associated with tables to provide
-- efficient backtracking.
--
-- TODO multi-dim tables with 'OnlyZero' need a static check!
--
-- TODO PointL , PointR need sanity checks for boundaries
--
-- TODO the sanity checks are acutally a VERY BIG TODO since currently we do
-- not protect against stupidity at all!
--
-- TODO have boxed tables for top-down parsing.
--
-- TODO combine forward and backward phases to simplify the external interface
-- to the programmer.
--
-- TODO include the notion of @interfaces@ into tables. With Outside
-- grammars coming up now, we need this.

module ADP.Fusion.Table.Array
--  ( MTbl      (..)
--  , BtTbl     (..)
  ( ITbl      (..)
--  , Backtrack (..)
  , ToBT (..)
  ) where

import           Control.Exception(assert)
import           Control.Monad.Primitive (PrimMonad)
import           Data.Vector.Fusion.Stream.Size (Size(Unknown))
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Unboxed as VU
import           GHC.Exts
import           Data.Bits

import           Data.PrimitiveArray -- (Z(..), (:.)(..), Subword(..), subword, PointL(..), pointL, PointR(..), pointR,topmostIndex, Outside(..))
import qualified Data.PrimitiveArray as PA

import           ADP.Fusion.Classes
import           ADP.Fusion.Multi.Classes
import           ADP.Fusion.Table.Axiom
import           ADP.Fusion.Table.Backtrack
import           ADP.Fusion.Table.Indices

import           Debug.Trace



-- ** Mutable fill-phase tables.

-- | The backtracking version.





-- TODO empty table @ms@ stuff

instance
  ( Monad m
  , Element ls (BS2I First Last)
  , PA.PrimArrayOps arr (BS2I First Last) x
  , MkStream m ls (BS2I First Last)
  ) => MkStream m (ls :!: ITbl m arr (BS2I First Last) x) (BS2I First Last) where
  -- outermost case. Grab inner indices, calculate the remainder of the
  -- set, return value
  mkStream (ls :!: ITbl c t _) Static s (BitSet b:>Interface i:>Interface j)
    = S.map (\z -> let (BitSet zb:>_:>Interface zj) = getIdx z  -- the bitset we get from the guy before us
                       here = (BitSet (b `xor` zb .|. zj):>Interface zj:>Interface j) -- everything missing, set common interface
                   in  ElmITbl (t PA.! here) here z
            )
    $ mkStream ls (Variable Check Nothing) s (BitSet (clearBit b j):>Interface i:>Interface j)
  -- generate all possible subsets of the index. With A @Variable
  -- _ Nothing@, there is something to the right that will fill up the set.
  mkStream (ls :!: ITbl c t _) (Variable Check Nothing) full (BitSet b:>Interface i:>Interface j)
    = S.flatten mk step Unknown
    $ mkStream ls (Variable Check Nothing) full (BitSet b:>Interface i:>Interface j)
    where mk z = return (z,Just $ BitSet 0:>Interface 0:>Interface 0)
          step (_,Nothing) = return $ S.Done
          step (z,Just s ) = return $ S.Yield (ElmITbl (t PA.! s) s z) (z,succSet full s)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  -- generate only those indices with the requested number of set bits
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (BS2I First Last)
  , PA.PrimArrayOps arr (BS2I First Last) x
  , MkStream mB ls (BS2I First Last)
  ) => MkStream mB (ls :!: BT (ITbl mF arr (BS2I First Last) x) mF mB r) (BS2I First Last) where
  mkStream (ls :!: BtITbl c arr bt) Static full (BitSet b:>Interface i:>Interface j)
    = S.map (\z -> let (BitSet zb:>Interface zi:>Interface zj) = getIdx z
                       here = BitSet (clearBit b j):>Interface i:>Interface zj
                       d = arr PA.! here
                   in ElmBtITbl' d (bt full here) here z)
    $ mkStream ls (Variable Check Nothing) full (BitSet (clearBit b j):>Interface i:>Interface (-1))
  mkStream (ls :!: BtITbl c arr bt) (Variable Check Nothing) full (BitSet b:>Interface i:>Interface j)
    = S.flatten mk step Unknown
    $ mkStream ls (Variable Check Nothing) full (BitSet b:>Interface i:>Interface j)
    where mk z = return (z,Just $ BitSet 0:>Interface 0:>Interface 0)
          step (_,Nothing) = return $ S.Done
          step (z,Just s ) = return $ S.Yield (ElmBtITbl' (arr PA.! s) (bt full s) s z) (z,succSet full s)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Outside PointL)
  , PA.PrimArrayOps arr (Outside PointL) x
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: ITbl m arr (Outside PointL) x) (Outside PointL) where
  mkStream (ls :!: ITbl c t _) Static lu (O (PointL (i:.j)))
    = let ms = minSize c in seq ms $ seq t $
    S.mapM (\s -> let O (PointL (h:.k)) = getIdx s
                  in  return $ ElmITbl (t PA.! O (pointL k j)) (O $ pointL k j) s)
    $ mkStream ls (Variable Check Nothing) lu (O . pointL i $ j + ms)
--  mkStream _ _ _ _ = error "mkStream / ITbl / Outside PointL not implemented"
  {-# INLINE mkStream #-}

instance
  ( Monad mB
  , Element ls (Outside PointL)
  , PA.PrimArrayOps arr (Outside PointL) x
  , MkStream mB ls (Outside PointL)
  ) => MkStream mB (ls :!: BT (ITbl mF arr (Outside PointL) x) mF mB r) (Outside PointL) where
  mkStream (ls :!: BtITbl c arr bt) Static lu (O (PointL (i:.j)))
    = let ms = minSize c in ms `seq`
    S.map (\s -> let O (PointL (h:.k)) = getIdx s
                     ix                = O $ pointL k j
                     d                 = arr PA.! ix
                 in ElmBtITbl' d (bt lu ix) ix s)
    $ mkStream ls (Variable Check Nothing) lu (O . pointL i $ j + ms)
--  mkStream _ _ _ _ = error "mkStream / BT ITbl / Outside PointL not implemented"
  {-# INLINE mkStream #-}

-- | TODO As soon as we don't do static checking on @EmptyOk/NonEmpty@
-- anymore, this works! If we check @c@, we immediately have fusion
-- breaking down!

{-
instance
  ( Monad m
  , Element ls Subword
  , PA.PrimArrayOps arr Subword x
  , MkStream m ls Subword
  ) => MkStream m (ls :!: ITbl m arr Subword x) Subword where
  mkStream (ls :!: ITbl c t _) Static lu (Subword (i:.j))
    = let ms = minSize c in ms `seq`
      S.mapM (\s -> let Subword (_:.l) = getIdx s
                    in  return $ ElmITbl (t PA.! subword l j) (subword l j) s)
    $ mkStream ls (Variable Check Nothing) lu (subword i $ j - ms) -- - minSize c)
  mkStream (ls :!: ITbl c t _) (Variable _ Nothing) lu (Subword (i:.j))
    = let ms = minSize c
          {- data PBI a = PBI !a !(Int#)
          mk s = let (Subword (_:.l)) = getIdx s ; !(I# jlm) = j-l-ms in return $ PBI s jlm
          step !(PBI s z) | 1# <- z >=# 0# = do let (Subword (_:.k)) = getIdx s
                                                return $ S.Yield (ElmITbl (t PA.! subword k (j-(I# z))) (subword k $ j-(I# z)) s) (PBI s (z -# 1#))
                          | otherwise = return S.Done
          -}
          {-
          mk s = let (Subword (_:.l)) = getIdx s in return (s :. j - l - ms)
          step (s:.z) | 1# <- z' >=# 0# = do let (Subword (_:.k)) = getIdx s
                                             return $ S.Yield (ElmITbl (t PA.! subword k (j-z)) (subword k $ j-z) s) (s:.z-1)
                      | otherwise = return S.Done
                      where !(I# z') = z
          -}
          mk s = let (Subword (_:.l)) = getIdx s in return (s :. j - l - ms)
          step (s:.z) | z>=0 = do let (Subword (_:.k)) = getIdx s
                                  return $ S.Yield (ElmITbl (t PA.! subword k (j-z)) (subword k $ j-z) s) (s:.z-1)
                      | otherwise = return S.Done
          {-# INLINE [1] mk #-}
          {-# INLINE [1] step #-}
      in ms `seq` S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) lu (subword i j)
  {-# INLINE mkStream #-}
-}

{-
instance
  ( Monad mB
  , Element ls Subword
  , MkStream mB ls Subword
  , PA.PrimArrayOps arr Subword x
  ) => MkStream mB (ls :!: BT (ITbl mF arr Subword x) mF mB r) Subword where
  mkStream (ls :!: BtITbl c arr bt)  Static lu (Subword (i:.j))
    = let ms = minSize c in ms `seq`
      S.map (\s -> let (Subword (_:.l)) = getIdx s
                       ix               = subword l j
                       d                = arr PA.! ix
                   in  ElmBtITbl' d (bt lu ix) ix s)
      $ mkStream ls (Variable Check Nothing) lu (subword i $ j - ms)
  mkStream (ls :!: BtITbl c arr bt) (Variable _ Nothing) lu (Subword (i:.j))
    = let ms = minSize c
          mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-ms)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                                 ix               = subword k (j-z)
                                 d                = arr PA.! ix
                             return $ S.Yield (ElmBtITbl' d (bt lu ix) ix s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in  ms `seq` S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) lu (subword i j)
  {-# INLINE mkStream #-}
-}

{-
instance
  ( Monad m
  , Element ls (Outside Subword)
  , PA.PrimArrayOps arr Subword x
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: ITbl m arr Subword x) (Outside Subword) where
  mkStream (ls :!: ITbl c t _) Static lu (O (Subword (i:.j)))
    = let ms = minSize c in ms `seq`
      S.mapM (\s -> let (O (Subword (_:.l))) = getIdx s
                    in  return $ ElmITbl (t PA.! (subword l j)) (O $ subword l j) s)
    $ mkStream ls (Variable Check Nothing) lu (O $ subword i $ j - ms) -- - minSize c)
  mkStream (ls :!: ITbl c t _) (Variable _ Nothing) lu (O (Subword (i:.j)))
    = let ms = minSize c
          mk s = let (O( Subword (_:.l))) = getIdx s in return (s :. j - l - ms)
          step (s:.z) | z>=0 = do let (O (Subword (_:.k))) = getIdx s
                                  return $ S.Yield (ElmITbl (t PA.! (subword k (j-z))) (O . subword k $ j-z) s) (s:.z-1)
                      | otherwise = return S.Done
          {-# INLINE [1] mk #-}
          {-# INLINE [1] step #-}
      in ms `seq` S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) lu (O $ subword i j)
  {-# INLINE mkStream #-}
-}

{-
instance
  ( Monad m
  , Element ls (Outside Subword)
  , PA.PrimArrayOps arr (Outside Subword) x
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: ITbl m arr (Outside Subword) x) (Outside Subword) where
  mkStream (ls :!: ITbl c t _) Static lu (O (Subword (i:.j)))
    = let ms = minSize c in ms `seq`
      S.mapM (\s -> let (O (Subword (_:.l))) = getIdx s
                    in  return $ ElmITbl (t PA.! (O $ subword l j)) (O $ subword l j) s)
    $ mkStream ls (Variable Check Nothing) lu (O $ subword i $ j - ms) -- - minSize c)
  mkStream (ls :!: ITbl c t _) (Variable _ Nothing) lu (O (Subword (i:.j)))
    = let ms = minSize c
          mk s = let (O( Subword (_:.l))) = getIdx s in return (s :. j - l - ms)
          step (s:.z) | z>=0 = do let (O (Subword (_:.k))) = getIdx s
                                  return $ S.Yield (ElmITbl (t PA.! (O $ subword k (j-z))) (O . subword k $ j-z) s) (s:.z-1)
                      | otherwise = return S.Done
          {-# INLINE [1] mk #-}
          {-# INLINE [1] step #-}
      in ms `seq` S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) lu (O $ subword i j)
  {-# INLINE mkStream #-}
-}




-- * Axiom for backtracking

-}

