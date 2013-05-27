{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module ADP.Fusion.Table where

import Control.Monad.Primitive
import Data.Array.Repa.Index
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU
import Data.Strict.Maybe
import Prelude hiding (Maybe(..))

import Data.Array.Repa.Index.Subword
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA

import ADP.Fusion.Classes



-- * Mutable table with adaptive storage.

data MTbl i x = forall m . (Monad m, PrimMonad m) => MTbl (ENZ i) (PA.MutArr m (Storage i x))

-- | The adaptive storage system.

class AdaptiveStorage i x where
  type Storage i x :: * -- specify boxed/unboxed stuff
  type StorageElm i x :: * -- single element to return
  fromStorage :: (Monad m, PrimMonad m) => x -> S.Stream m (z) -> S.Stream m (z:!:StorageElm i x)



-- * Instances

instance AdaptiveStorage i Int where
  type Storage i Int = PA.Unboxed i Int
  type StorageElm i Int = Int
  fromStorage x = S.map (:!:x)
  {-# INLINE fromStorage #-}

instance Build (MTbl i x)

instance
  ( Elms ls (is:.i)
  ) => Elms (ls :!: MTbl (is:.i) x) (is:.i) where
  data Elm (ls :!: MTbl (is:.i) x) (is:.i) = ElmMTbl !(Elm ls (is:.i)) !(StorageElm (is:.i) x) !(is:.i)
  type Arg (ls :!: MTbl (is:.i) x) = Arg ls :. StorageElm (is:.i) x
  getArg !(ElmMTbl ls x _) = getArg ls :. x
  getIdx !(ElmMTbl _ _  i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls (is:.i)
  , MkStream m ls (is:.i)
  ) => MkStream m (ls:!:MTbl (is:.i) x) (is:.i) where
  mkStream (ls :!: MTbl enz tbl) os is
    = undefined
    -- use os is and the current stream to generate indices
    $ mkStream ls os is
  {-# INLINE mkStream #-}

{-

-- * Immutable tables.

data Tbl x = Tbl !(PA.Unboxed (Z:.Subword) x)

instance Build (Tbl x)

instance
  ( Elms ls Subword
  ) => Elms (ls :!: Tbl x) Subword where
  data Elm (ls :!: Tbl x) Subword = ElmTbl !(Elm ls Subword) !x !Subword
  type Arg (ls :!: Tbl x) = Arg ls :. x
  getArg !(ElmTbl ls x _) = getArg ls :. x
  getIdx !(ElmTbl _ _ idx) = idx
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:Tbl x) Subword where
  mkStream !(ls:!:Tbl xs) Outer !ij@(Subword (i:.j)) = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmTbl s (xs PA.! (Z:.subword l j)) (subword l j)) $ mkStream ls (Inner Check Nothing) ij
  mkStream !(ls:!:Tbl xs) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    mk !s = let (Subword (k:.l)) = getIdx s
                le = l -- TODO need to add ENE here ! -- + case ene of { EmptyT -> 0 ; NoEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in  return (s :!: l :!: l')
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = return $ S.Yield (ElmTbl s (xs PA.! (Z:.subword k l)) (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}



-- * Backtracking tables.

data BtTbl m x b = BtTbl ENE !(PA.Unboxed (Z:.Subword) x) !(Subword -> m (S.Stream m b))

instance Build (BtTbl m x b)

instance
  ( Monad m
  , Elms ls Subword
  ) => Elms (ls :!: BtTbl m x b) Subword where
  data Elm (ls :!: BtTbl m x b) Subword = ElmBtTbl !(Elm ls Subword) !x !(m (S.Stream m b)) !Subword
  type Arg (ls :!: BtTbl m x b) = Arg ls :. (x,m (S.Stream m b))
  getArg !(ElmBtTbl ls x b _) = getArg ls :. (x,b)
  getIdx !(ElmBtTbl _  _ _ i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , VU.Unbox x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: BtTbl m x b) Subword where
  mkStream !(ls:!:BtTbl ene xs f) Outer !ij@(Subword (i:.j))
    = S.map (\s -> let (Subword (k:.l)) = getIdx s in ElmBtTbl s (xs PA.! (Z:.subword l j)) (f $ subword l j) (subword l j))
    $ mkStream ls (Inner Check Nothing) (subword i $ case ene of { EmptyT -> j ; NoEmptyT -> j-1 })
  mkStream !(ls:!:BtTbl ene xs f) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    mk !s = let (Subword (k:.l)) = getIdx s
                le = l + case ene of { EmptyT -> 0 ; NoEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in  return (s:!:l:!: l')
    step !(s:!:k:!:l)
      | l > j     = return $ S.Done
      | otherwise = return $ S.Yield (ElmBtTbl s (xs PA.! (Z:.subword k l)) (f $ subword k l) (subword k l)) (s:!:k:!:l+1)
  {-# INLINE mkStream #-}



-- * Unboxed mutable table for the forward phase in one dimension.

data MTbl xs = MTbl !ENE !xs

instance
  ( ValidIndex ls Subword
  , Monad m
  , PA.MPrimArrayOps arr (Z:.Subword) x
  ) => ValidIndex (ls:!:MTbl (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  validIndex (_  :!: MTbl ZeroT _) _ _ = error "table with ZeroT found, there is no reason (actually: no implementation) for 1-dim ZeroT tables"
  validIndex (ls :!: MTbl ene tbl) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
    let (_,Z:.Subword (0:.n)) = PA.boundsM tbl
        minsize = max b (if ene==EmptyT then 0 else 1)
    in  i>=a && i+minsize<=j && j<=n-c && validIndex ls abc ij
  {-# INLINE validIndex #-}
  getParserRange (ls :!: MTbl ene _) ix = let (a:!:b:!:c) = getParserRange ls ix in if ene==EmptyT then (a:!:b:!:c) else (a:!:b+1:!:c)
  {-# INLINE getParserRange #-}

instance Build (MTbl xs)

instance
  ( Monad m
  , Elms ls Subword
  ) => Elms (ls :!: MTbl (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  data Elm (ls :!: MTbl (PA.MutArr m (arr (Z:.Subword) x))) Subword = ElmMTbl !(Elm ls Subword) !x !Subword
  type Arg (ls :!: MTbl (PA.MutArr m (arr (Z:.Subword) x))) = Arg ls :. x
  getArg !(ElmMTbl ls x _) = getArg ls :. x
  getIdx !(ElmMTbl _ _ i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( PrimMonad m
  , PA.MPrimArrayOps arr (Z:.Subword) x
  , Elms ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls:!:MTbl (PA.MutArr m (arr (Z:.Subword) x))) Subword where
  mkStream !(ls:!:MTbl ene tbl) Outer !ij@(Subword (i:.j))
    = S.mapM (\s -> let (Subword (_:.l)) = getIdx s in PA.readM tbl (Z:.subword l j) >>= \z -> return $ ElmMTbl s z (subword l j))
    $ mkStream ls (Inner Check Nothing) (subword i $ case ene of { EmptyT -> j ; NoEmptyT -> j-1 })
  mkStream !(ls:!:MTbl ene tbl) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    mk !s = let (Subword (_:.l)) = getIdx s
                le = l + case ene of { EmptyT -> 0 ; NoEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in return (s :!: l :!: l')
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = PA.readM tbl (Z:.subword k l) >>= \z -> return $ S.Yield (ElmMTbl s z (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}



{-

-- ** multi-tape generalization: empty / nonempty

instance
  ( ValidIndex ls (is:.i)
  , Monad m
  , PA.MPrimArrayOps arr (is:.i) x
  ) => ValidIndex (ls :!: MTbl (PA.MutArr m (arr (is:.i) x))) (is:.i) where
    validIndex (ls :!: MTbl ene tbl) (is:.i) =
      let
      in  undefined

instance
  ( Monad m
  ) => Elms (ls :!: MTbl (PA.MutArr m (arr (is:.i) x))) (is:.i) where

instance
  ( Monad m
  ) => MkStream m (ls:!: MTbl (PA.MutArr m (arr (is:.i) x))) (is:.i) where
  mkStream !(ls:!:MTbl ene tbl) io is
    = undefined



{-
data GMtbl i x = forall m . GMtbl (ENEdim i) (PA.MutArr m (Storage i x))

-}

-}

-}

