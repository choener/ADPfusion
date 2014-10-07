
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

module ADP.Fusion.Table.Array
  ( MTbl      (..)
  , BtTbl     (..)
  , ITbl      (..)
  , Backtrack (..)
  , ToBT (..)
  ) where

import           Control.Monad.Primitive (PrimMonad)
import           Data.Strict.Tuple hiding (uncurry)
import           Data.Vector.Fusion.Stream.Size (Size(Unknown))
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Unboxed as VU
import           GHC.Exts

import           Data.PrimitiveArray (Z(..), (:.)(..), Subword(..), subword, PointL(..), pointL, PointR(..), pointR,topmostIndex)
import qualified Data.PrimitiveArray as PA

import           ADP.Fusion.Classes
import           ADP.Fusion.Multi.Classes
import           ADP.Fusion.Table.Axiom
import           ADP.Fusion.Table.Backtrack
import           ADP.Fusion.Table.Indices



-- ** Mutable fill-phase tables.

-- | Mutable table with table constraints, a mutable array, and a function
-- evaluating given an index.

data MTbl m arr i x where
  MTbl :: !(TblConstraint i) -> !(PA.MutArr m (arr i x)) -> !(i -> m x) -> MTbl m arr i x

-- | Backtracking table.

data BtTbl m arr i x r where
  BtTbl :: !(TblConstraint i) -> !(arr i x) -> !(i -> m (S.Stream m r)) -> BtTbl m arr i x r

-- | Immutable table.

data ITbl m arr i x where
  ITbl :: !(TblConstraint i) -> !(arr i x) -> !(i -> m x) -> ITbl m arr i x

-- | The backtracking version.

data Backtrack t r where
  Backtrack :: !t -> !(forall m i . i -> m (S.Stream m r)) -> Backtrack t r

instance ToBT (ITbl mF arr i x) mF mB r where
  --data BT (ITbl mF arr i x) mF mB i r = BtITbl (ITbl mF arr i x) (forall a . mF a -> mB a)  (i -> mB (S.Stream mB r))
  data BT (ITbl mF arr i x) mF mB r = BtITbl !(TblConstraint i) !(arr i x) (i -> mB (S.Stream mB r))
  type BtIx (ITbl mF arr i x) = i
  toBT (ITbl c arr _) _ bt = BtITbl c arr bt
  {-# INLINE toBT #-}

-- * Instances. The instances should look very much alike. As a measure of
-- code safety I'm putting them next to each other.

-- ** General instances for 'MTbl' / 'BtTbl'

instance Build (MTbl m arr i x)

instance Build (BtTbl m arr i x r)

instance Build (ITbl m arr i x)

instance Build (Backtrack t r)

instance Element ls i => Element (ls :!: MTbl m arr i x) i where
  data Elm (ls :!: MTbl m arr i x) i = ElmMTbl !x !i !(Elm ls i)
  type Arg (ls :!: MTbl m arr i x)   = Arg ls :. x
  getArg (ElmMTbl x _ ls) = getArg ls :. x
  getIdx (ElmMTbl _ i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance Element ls i => Element (ls :!: BtTbl m arr i x r) i where
  data Elm (ls :!: BtTbl m arr i x r) i = ElmBtTbl !x !(m (S.Stream m r)) !i !(Elm ls i)
  type Arg (ls :!: BtTbl m arr i x r)   = Arg ls :. (x, m (S.Stream m r))
  getArg (ElmBtTbl x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtTbl _ _ k _ ) = k
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance Element ls i => Element (ls :!: ITbl m arr i x) i where
  data Elm (ls :!: ITbl m arr i x) i = ElmITbl !x !i !(Elm ls i)
  type Arg (ls :!: ITbl m arr i x)   = Arg ls :. x
  getArg (ElmITbl x _ ls) = getArg ls :. x
  getIdx (ElmITbl _ i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance Element ls i => Element (ls :!: (Backtrack (ITbl m arr i x) r)) i where
  data Elm (ls :!: (Backtrack (ITbl m arr i x) r)) i = ElmBtITbl !x !(m (S.Stream m r)) !i (Elm ls i)
  type Arg (ls :!: (Backtrack (ITbl m arr i x) r))   = Arg ls :. (x, m (S.Stream m r))
  getArg (ElmBtITbl x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtITbl _ _ i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance Element ls i => Element (ls :!: (BT (ITbl mF arr i x) mF mB r)) i where
  data Elm (ls :!: (BT (ITbl mF arr i x) mF mB r)) i = ElmBtITbl' !x !(mB (S.Stream mB r)) !i !(Elm ls i)
  type Arg (ls :!: (BT (ITbl mF arr i x) mF mB r))   = Arg ls :. (x, mB (S.Stream mB r))
  getArg (ElmBtITbl' x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtITbl' _ _ i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}




-- ** @Subword@ indexing

instance ModifyConstraint (MTbl m arr Subword x) where
  toNonEmpty (MTbl _ arr f) = MTbl NonEmpty arr f
  toEmpty    (MTbl _ arr f) = MTbl EmptyOk  arr f
  {-# INLINE toNonEmpty #-}
  {-# INLINE toEmpty #-}

instance ModifyConstraint (BtTbl m arr Subword x r) where
  toNonEmpty (BtTbl _ arr f) = BtTbl NonEmpty arr f
  toEmpty    (BtTbl _ arr f) = BtTbl EmptyOk  arr f
  {-# INLINE toNonEmpty #-}
  {-# INLINE toEmpty #-}

instance ModifyConstraint (ITbl m arr Subword x) where
  toNonEmpty (ITbl _ arr f) = ITbl NonEmpty arr f
  toEmpty    (ITbl _ arr f) = ITbl EmptyOk  arr f
  {-# INLINE toNonEmpty #-}
  {-# INLINE toEmpty #-}

instance ModifyConstraint (Backtrack (ITbl m arr Subword x) r) where
  toNonEmpty (Backtrack (ITbl _ arr f) bt) = Backtrack (ITbl NonEmpty arr f) bt
  toEmpty    (Backtrack (ITbl _ arr f) bt) = Backtrack (ITbl EmptyOk  arr f) bt
  {-# INLINE toNonEmpty #-}
  {-# INLINE toEmpty #-}

instance ModifyConstraint (BT (ITbl mF arr Subword x) mF mB r) where
  toNonEmpty (BtITbl _ arr bt) = BtITbl NonEmpty arr bt
  toEmpty    (BtITbl _ arr bt) = BtITbl EmptyOk  arr bt
  {-# INLINE toNonEmpty #-}
  {-# INLINE toEmpty #-}

instance
  ( Monad m
  , PrimMonad m
  , Element ls Subword
  , MkStream m ls Subword
  , PA.MPrimArrayOps arr Subword x
  ) => MkStream m (ls :!: MTbl m arr Subword x) Subword where
  mkStream (ls :!: MTbl c t _) Static (Subword (i:.j))
    = S.mapM (\s -> let Subword (_:.l) = getIdx s
                    in  PA.readM t (subword l j) >>= \z -> return $ ElmMTbl z (subword l j) s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - minSize c)
  mkStream (ls :!: MTbl c t _) (Variable _ Nothing) (Subword (i:.j))
    = let mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-minSize c)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                             y <- PA.readM t (subword k (j-z))
                             return $ S.Yield (ElmMTbl y (subword k $ j-z) s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in  S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  , PA.PrimArrayOps arr Subword x
  ) => MkStream m (ls :!: BtTbl m arr Subword x r) Subword where
  mkStream (ls :!: BtTbl c t f) Static (Subword (i:.j))
    = S.map (\s -> let Subword (_:.l) = getIdx s
                       ix             = subword l j
                       d              = t PA.! ix
                   in  ElmBtTbl d (f ix) ix s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - minSize c)
  mkStream (ls :!: BtTbl c t f) (Variable _ Nothing) (Subword (i:.j))
    = let mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-minSize c)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                                 ix               = subword k (j-z)
                                 d                = t PA.! ix
                             return $ S.Yield (ElmBtTbl d (f ix) ix s) (s:.z-1)
            | otherwise = return S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in  S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

-- | TODO As soon as we don't do static checking on @EmptyOk/NonEmpty@
-- anymore, this works! If we check @c@, we immediately have fusion
-- breaking down!

instance
  ( Monad m
  , Element ls Subword
  , PA.PrimArrayOps arr Subword x
  , MkStream m ls Subword
  ) => MkStream m (ls :!: ITbl m arr Subword x) Subword where
  mkStream (ls :!: ITbl c t _) Static (Subword (i:.j))
    = let ms = minSize c in ms `seq`
      S.mapM (\s -> let Subword (_:.l) = getIdx s
                    in  return $ ElmITbl (t PA.! subword l j) (subword l j) s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - ms) -- - minSize c)
  mkStream (ls :!: ITbl c t _) (Variable _ Nothing) (Subword (i:.j))
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
      in ms `seq` S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

-- TODO broken!

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  , PA.PrimArrayOps arr Subword x
  ) => MkStream m (ls :!: Backtrack (ITbl m arr Subword x) r) Subword where
  mkStream (ls :!: Backtrack (ITbl c t _) bt) Static (Subword (i:.j))
    = S.mapM (\s -> let Subword (_:.l) = getIdx s
                        ix             = subword l j
                        d              = t PA.! ix
                    in  return $ ElmBtITbl d (bt ix) ix s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - minSize c)
  mkStream (ls :!: Backtrack (ITbl c t _) bt) (Variable _ Nothing) (Subword (i:.j))
    = let mk s = let (Subword (_:.l)) = getIdx s in return (s, j - l - minSize c)
          step (s,z) | z>=0 = do let (Subword (_:.k)) = getIdx s
                                     ix = subword k (j-z)
                                     d = t PA.! ix
                                 return $ S.Yield (ElmBtITbl d (bt ix) ix s) (s,z-1)
                     | otherwise = return S.Done
          {-# INLINE [1] mk #-}
          {-# INLINE [1] step #-}
      in S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

instance
  ( Monad mB
  , Element ls Subword
  , MkStream mB ls Subword
  , PA.PrimArrayOps arr Subword x
  ) => MkStream mB (ls :!: BT (ITbl mF arr Subword x) mF mB r) Subword where
  mkStream (ls :!: BtITbl c arr bt)  Static (Subword (i:.j))
    = let ms = minSize c in ms `seq`
      S.map (\s -> let (Subword (_:.l)) = getIdx s
                       ix               = subword l j
                       d                = arr PA.! ix
                   in  ElmBtITbl' d (bt ix) ix s)
      $ mkStream ls (Variable Check Nothing) (subword i $ j - ms)
  mkStream (ls :!: BtITbl c arr bt) (Variable _ Nothing) (Subword (i:.j))
    = let ms = minSize c
          mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-ms)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                                 ix               = subword k (j-z)
                                 d                = arr PA.! ix
                             return $ S.Yield (ElmBtITbl' d (bt ix) ix s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in  ms `seq` S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}



-- ** @(is:.i)@ indexing

instance
  ( Monad m
  , PrimMonad m
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , Element ls (is:.i)
  , PA.MPrimArrayOps arr (is:.i) x
  , MkStream m ls (is:.i)
  ) => MkStream m (ls :!: MTbl m arr (is:.i) x) (is:.i) where
  mkStream (ls :!: MTbl c t _) vs is
    = S.mapM (\(Tr s _ i) -> PA.readM t i >>= \z -> return $ ElmMTbl z i s)
    . tableIndices c vs is
    . S.map (\s -> Tr s Z (getIdx s))
    $ mkStream ls (tableStaticVar vs is) (tableStreamIndex c vs is)
  {-# INLINE mkStream #-}

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , MkStream m ls (is:.i)
  , PA.PrimArrayOps arr (is:.i) x
  ) => MkStream m (ls :!: BtTbl m arr (is:.i) x r) (is:.i) where
  mkStream (ls :!: BtTbl c t f) vs is
    = S.map (\(Tr s _ i) -> ElmBtTbl (t PA.! i) (f i) i s)
    . tableIndices c vs is
    . S.map (\s -> Tr s Z (getIdx s))
    $ mkStream ls (tableStaticVar vs is) (tableStreamIndex c vs is)
  {-# INLINE mkStream #-}

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , MkStream m ls (is:.i)
  , PA.PrimArrayOps arr (is:.i) x
  ) => MkStream m (ls :!: ITbl m arr (is:.i) x) (is:.i) where
  mkStream (ls :!: ITbl c t _) vs is
    = S.map (\(Tr s _ i) -> ElmITbl (t PA.! i) i s)
    . tableIndices c vs is
    . S.map (\s -> Tr s Z (getIdx s))
    $ mkStream ls (tableStaticVar vs is) (tableStreamIndex c vs is)
  {-# INLINE mkStream #-}

instance
  ( Monad mB
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , MkStream mB ls (is:.i)
  , PA.PrimArrayOps arr (is:.i) x
  ) => MkStream mB (ls :!: BT (ITbl mF arr (is:.i) x) mF mB r) (is:.i) where
  mkStream (ls :!: BtITbl c arr bt) vs is
    = S.map (\(Tr s _ i) -> ElmBtITbl' (arr PA.! i) (bt i) i s)
    . tableIndices c vs is
    . S.map (\s -> Tr s Z (getIdx s))
    $ mkStream ls (tableStaticVar vs is) (tableStreamIndex c vs is)
  {-# INLINE mkStream #-}



-- * Axiom for backtracking

instance (PA.ExtShape i, PA.PrimArrayOps arr i x) => Axiom (BtTbl m arr i x r) where
  type S (BtTbl m arr i x r) = m (S.Stream m r)
  axiom (BtTbl _ arr f) = f (uncurry topmostIndex $ PA.bounds arr)
  {-# INLINE axiom #-}

instance (PA.ExtShape i, PA.PrimArrayOps arr i x) => Axiom (Backtrack (ITbl m arr i x) r) where
  type S (Backtrack (ITbl m arr i x) r) = m (S.Stream m r)
  axiom (Backtrack (ITbl _ arr _) f) = f . uncurry topmostIndex $ PA.bounds arr
  {-# INLINE axiom #-}

instance (PA.ExtShape i, PA.PrimArrayOps arr i x) => Axiom (BT (ITbl mF arr i x) mF mB r) where
  type S (BT (ITbl mF arr i x) mF mB r) = mB (S.Stream mB r)
  axiom (BtITbl c arr bt) = bt . uncurry topmostIndex $ PA.bounds arr
  {-# INLINE axiom #-}

