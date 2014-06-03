{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

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

module ADP.Fusion.Table where

import           Control.Monad.Primitive
import           Data.Array.Repa.Index
import           Data.Array.Repa.Shape
import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU

import           Data.Array.Repa.ExtShape
import           Data.Array.Repa.Index.Points
import           Data.Array.Repa.Index.Subword
import qualified Data.PrimitiveArray as PA
import qualified Data.PrimitiveArray.Zero as PA
import qualified Data.PrimitiveArray.FillTables as PA

import ADP.Fusion.Classes
import ADP.Fusion.Multi.Classes



-- | A table with mutable elements and attached table constraints.

data MTbl i xs = MTbl !(TblConstraint i) !xs

-- | A single-dimensional table. The index type needs a @Z:.@ when creating the
-- internal @arr@.

mTblS :: TblConstraint i -> PA.MutArr m (arr i x) -> MTbl i (PA.MutArr m (arr i x))
mTblS = MTbl
{-# INLINE mTblS #-}

-- | General multi-dimensional tables. Here, index types and table constraints
-- just match up.

mTblD :: TblConstraint i -> PA.MutArr m (arr i x) -> MTbl i (PA.MutArr m (arr i x))
mTblD = MTbl
{-# INLINE mTblD #-}

instance Build (MTbl i x)

instance ModifyConstraint (MTbl Subword arr) where
  toNonEmpty (MTbl _ arr) = MTbl NonEmpty arr
  toEmpty    (MTbl _ arr) = MTbl EmptyOk  arr
  {-# INLINE toNonEmpty #-}
  {-# INLINE toEmpty #-}

type MTblSubword m arr x   = MTbl Subword (PA.MutArr m (arr Subword x))
type MTblMulti   m arr x i = MTbl i       (PA.MutArr m (arr i       x))



-- ** Single-dimensional table using a 'Subword' index.

instance
  ( Element ls Subword
  ) => Element (ls :!: MTblSubword m arr x) Subword where
  data Elm (ls :!: MTblSubword m arr x) Subword = ElmMtSw !x !Subword !(Elm ls Subword)
  type Arg (ls :!: MTblSubword m arr x)         = Arg ls :. x
  getArg (ElmMtSw x _ ls) = getArg ls :. x
  getIdx (ElmMtSw x i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , PrimMonad m
  , Element ls Subword
  , MkStream m ls Subword
  , PA.MPrimArrayOps arr Subword x
  ) => MkStream m (ls :!: MTblSubword m arr x) Subword where
  mkStream (ls :!: MTbl c t) Static (Subword (i:.j))
    = S.mapM (\s -> let Subword (_:.l) = getIdx s
                    in  PA.readM t (subword l j) >>= \z -> return $ ElmMtSw z (subword l j) s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - minSize c)
  mkStream (ls :!: MTbl c t) (Variable _ Nothing) (Subword (i:.j))
    = let mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-minSize c)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                             y <- PA.readM t (subword k (j-z))
                             return $ S.Yield (ElmMtSw y (subword k $ j-z) s) (s:.z-1)
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in  S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}



-- ** General multi-dimensional tables.

instance Element ls (is:.i) => Element (ls :!: MTblMulti m arr x (is:.i)) (is:.i) where
  data Elm (ls :!: MTblMulti m arr x (is:.i)) (is:.i) = ElmMTbl !x !(is:.i) !(Elm ls (is:.i))
  type Arg (ls :!: MTblMulti m arr x (is:.i))         = Arg ls :. x
  getArg (ElmMTbl x _ ls) = getArg ls :. x
  getIdx (ElmMTbl _ i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , PrimMonad m
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , Element ls (is:.i)
  , PA.MPrimArrayOps arr (is:.i) x
  , MkStream m ls (is:.i)
  ) => MkStream m (ls :!: MTblMulti m arr x (is:.i)) (is:.i) where
  mkStream (ls :!: MTbl c t) vs is
    = S.mapM (\(Tr s _ i) -> PA.readM t i >>= \z -> return $ ElmMTbl z i s)
    . tableIndices c vs is
    . S.map (\s -> Tr s Z (getIdx s))
    $ mkStream ls (tableStaticVar vs is) (tableStreamIndex c vs is)
  {-# INLINE mkStream #-}



-- * With 'tableIndices' we create a stream of legal indices for this table. We
-- need 'tableIndices' in multi-dimensional tables as the type of the
-- multi-dimensional indices is generic.
--
-- TODO own module?

class TableIndices i where
  tableIndices :: (Monad m) => TblConstraint i -> IxSV i -> i -> S.Stream m (Triple z j i) -> S.Stream m (Triple z j i)

instance TableIndices Z where
  tableIndices _ _ _ = id
  {-# INLINE tableIndices #-}

instance TableIndices is => TableIndices (is:.Subword) where
  tableIndices (cs:.c) (vs:.Static) (is:.Subword (i:.j))
    = S.map (\(Tr s (x:.Subword (_:.l)) ys) -> Tr s x (is:.subword l j)) -- constraint handled: tableStreamIndex
    . tableIndices cs vs is
    . S.map moveIdxTr
  tableIndices (cs:.OnlyZero) _ _ = error "write me"
  tableIndices (cs:.c) (vs:.Variable _ Nothing) (is:.Subword (i:.j))
    = S.flatten mk step Unknown
    . tableIndices cs vs is
    . S.map moveIdxTr
    where mk (Tr s (y:.Subword (_:.l)) xs) = return $ Pn s y xs l (j-l-minSize c)
          step (Pn s y xs k z)
            | z>= 0     = return $ S.Yield (Tr s y (xs:.subword k (j-z))) (Pn s y xs k (z-1))
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
  {-# INLINE tableIndices #-}

instance TableIndices is => TableIndices (is:.PointL) where
  tableIndices (cs:.c) (vs:.Static) (is:.PointL (i:.j))
    = id -- staticCheck (i<=j)
    . S.map (\(Tr s (x:.PointL (_:.l)) ys) -> Tr s x (is:.pointL l j)) -- constraint handled: tableStreamIndex
    . tableIndices cs vs is
    . S.map moveIdxTr
  tableIndices (cs:.OnlyZero) _ _ = error "write me"
  tableIndices (cs:.c) (vs:.Variable _ Nothing) (is:.PointL (i:.j))
    = S.flatten mk step Unknown
    . tableIndices cs vs is
    . S.map moveIdxTr
    where mk (Tr s (y:.PointL (_:.l)) xs) = return $ Pn s y xs l (j-l-minSize c)
          step (Pn s y xs k z)
            | z>= 0     = return $ S.Yield (Tr s y (xs:.pointL k (j-z))) (Pn s y xs k (z-1))
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
  {-# INLINE tableIndices #-}

instance TableIndices is => TableIndices (is:.PointR) where
  tableIndices (cs:.c) (vs:.Static) (is:.PointR (i:.j))
    = S.map (\(Tr s (x:.PointR (_:.l)) ys) -> Tr s x (is:.pointR l j)) -- constraint handled: tableStreamIndex
    . tableIndices cs vs is
    . S.map moveIdxTr
  tableIndices (cs:.OnlyZero) _ _ = error "write me"
  tableIndices (cs:.c) (vs:.Variable _ Nothing) (is:.PointR (i:.j))
    = S.flatten mk step Unknown
    . tableIndices cs vs is
    . S.map moveIdxTr
    where mk (Tr s (y:.PointR (_:.l)) xs) = return $ Pn s y xs l (j-l-minSize c)
          step (Pn s y xs k z)
            | z>= 0     = return $ S.Yield (Tr s y (xs:.pointR k (j-z))) (Pn s y xs k (z-1))
            | otherwise = return $ S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
  {-# INLINE tableIndices #-}



-- * Backtracking tables. These wrap the fully-calculated DP matrices and also
-- capture the backtracking function.

-- | Capture table constraints, the table, and the backtracking function.
--
-- TODO Check strictness annotation in the backtracking function (we want the
-- function to be expanded early).

data BtTbl i xs f = BtTbl !(TblConstraint i) !xs !f

btTblS :: TblConstraint i -> arr i x -> (i -> m (S.Stream m b)) -> BtTbl i (arr i x) (i -> m (S.Stream m b))
btTblS = BtTbl
{-# INLINE btTblS #-}

btTblD :: TblConstraint i -> arr i      x -> (i -> m (S.Stream m b)) -> BtTbl i (arr i      x) (i -> m (S.Stream m b))
btTblD = BtTbl
{-# INLINE btTblD #-}

instance Build (BtTbl i x f)

instance ModifyConstraint (BtTbl Subword arr f) where
  toNonEmpty (BtTbl _ arr f) = BtTbl NonEmpty arr f
  toEmpty    (BtTbl _ arr f) = BtTbl EmptyOk  arr f
  {-# INLINE toNonEmpty #-}
  {-# INLINE toEmpty #-}

type BtTblSubword m arr x   b = BtTbl Subword (arr Subword x) (Subword -> m (S.Stream m b))
type BtTblMulti   m arr x i b = BtTbl i       (arr i            x) (i       -> m (S.Stream m b))



-- ** Single-dimensional table using a 'Subword' index.

instance
  ( Element ls Subword
  ) => Element (ls :!: BtTblSubword m arr x b) Subword where
  data Elm (ls :!: BtTblSubword m arr x b) Subword = ElmBttSw !x !(m (S.Stream m b)) !Subword !(Elm ls Subword)
  type Arg (ls :!: BtTblSubword m arr x b)         = Arg ls :. (x , m (S.Stream m b))
  getArg (ElmBttSw x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBttSw _ _ k _ ) = k
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  , PA.PrimArrayOps arr Subword x
  ) => MkStream m (ls :!: BtTblSubword m arr x b) Subword where
  mkStream (ls :!: BtTbl c t f) Static (Subword (i:.j))
    = S.map (\s -> let Subword (_:.l) = getIdx s
                       ix             = subword l j
                       d              = t PA.! ix
                   in  ElmBttSw d (f ix) ix s)
    $ mkStream ls (Variable Check Nothing) (subword i $ j - minSize c)
  mkStream (ls :!: BtTbl c t f) (Variable _ Nothing) (Subword (i:.j))
    = let mk s = let (Subword (_:.l)) = getIdx s in return (s:.j-l-minSize c)
          step (s:.z)
            | z>=0      = do let (Subword (_:.k)) = getIdx s
                                 ix               = subword k (j-z)
                                 d                = t PA.! ix
                             return $ S.Yield (ElmBttSw d (f ix) ix s) (s:.z-1)
            | otherwise = return S.Done
          {-# INLINE [1] mk   #-}
          {-# INLINE [1] step #-}
      in  S.flatten mk step Unknown $ mkStream ls (Variable NoCheck Nothing) (subword i j)
  {-# INLINE mkStream #-}

instance Element ls (is:.i) => Element (ls :!: BtTblMulti m arr x (is:.i) b) (is:.i) where
  data Elm (ls :!: BtTblMulti m arr x (is:.i) b) (is:.i) = ElmBtTbl !x !(m (S.Stream m b)) !(is:.i) !(Elm ls (is:.i))
  type Arg (ls :!: BtTblMulti m arr x (is:.i) b)         = Arg ls :. (x, m (S.Stream m b))
  getArg (ElmBtTbl x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtTbl _ _ k _ ) = k
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , MkStream m ls (is:.i)
  , PA.PrimArrayOps arr (is:.i) x
  ) => MkStream m (ls :!: BtTblMulti m arr x (is:.i) b) (is:.i) where
  mkStream (ls :!: BtTbl c t f) vs is
    = S.map (\(Tr s _ i) -> ElmBtTbl (t PA.! i) (f i) i s)
    . tableIndices c vs is
    . S.map (\s -> Tr s Z (getIdx s))
    $ mkStream ls (tableStaticVar vs is) (tableStreamIndex c vs is)
  {-# INLINE mkStream #-}

{-
data BtTbl i xs f = BtTbl !(ENZ i) !xs !f -- (i -> m (S.Stream m b))

btTbl :: ENZ i -> xs -> f -> BtTbl i xs f --(i -> m (S.Stream m b)) -> BtTbl m i xs b
btTbl = BtTbl
{-# INLINE btTbl #-}

type DefBtTbl m isi x b = BtTbl isi (PA.Unboxed isi x) (isi -> m (S.Stream m b))
type SwBtTbl m x b = BtTbl Subword (PA.Unboxed (Z:.Subword) x) (Subword -> m (S.Stream m b))

instance Build (BtTbl i xs f)

instance
  ( Elms ls Subword
  ) => Elms (ls :!: SwBtTbl m x b) Subword where
  data Elm (ls :!: SwBtTbl m x b) Subword = ElmSwBtTbl !(Elm ls Subword) !(x,m (S.Stream m b)) !Subword
  type Arg (ls :!: SwBtTbl m x b) = Arg ls :. (x,m (S.Stream m b))
  getArg !(ElmSwBtTbl ls x _) = getArg ls :. x
  getIdx !(ElmSwBtTbl _ _  i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls Subword
  , VU.Unbox x
  , MkStream m ls Subword
  ) => MkStream m (ls :!: SwBtTbl m x b) Subword where
  mkStream !(ls:!:BtTbl ene tbl f) Outer !ij@(Subword (i:.j))
    = S.mapM (\s -> let (Subword (_:.l)) = getIdx s in return $ ElmSwBtTbl s (tbl PA.! (Z:.subword l j), f $ subword l j) (subword l j))
    $ mkStream ls (Inner Check Nothing) (subword i $ case ene of { EmptyT -> j ; NonEmptyT -> j-1 })
  mkStream !(ls:!:BtTbl ene tbl f) (Inner _ szd) !ij@(Subword (i:.j)) = S.flatten mk step Unknown $ mkStream ls (Inner NoCheck Nothing) ij where
    mk !s = let (Subword (_:.l)) = getIdx s
                le = l + case ene of { EmptyT -> 0 ; NonEmptyT -> 1}
                l' = case szd of Nothing -> le
                                 Just z  -> max le (j-z)
            in return (s :!: l :!: l')
    step !(s :!: k :!: l)
      | l > j = return S.Done
      | otherwise = return $ S.Yield (ElmSwBtTbl s (tbl PA.! (Z:.subword k l), f $ subword k l) (subword k l)) (s :!: k :!: l+1)
  {-# INLINE mkStream #-}

instance
  ( ValidIndex ls Subword
  , VU.Unbox x
  ) => ValidIndex (ls :!: SwBtTbl m x b) Subword where
  validIndex (_  :!: BtTbl ZeroT _ _) _ _ = error "table with ZeroT found, there is no reason (actually: no implementation) for 1-dim ZeroT tables"
  validIndex (ls :!: BtTbl ene tbl _) abc@(a:!:b:!:c) ij@(Subword (i:.j)) =
    let (_,Z:.Subword (0:.n)) = PA.bounds tbl
        minsize = max b (if ene==EmptyT then 0 else 1)
    in  i>=a && i+minsize<=j && j<=n-c && validIndex ls abc ij
  {-# INLINE validIndex #-}
  getParserRange (ls :!: BtTbl ene _ f) ix = let (a:!:b:!:c) = getParserRange ls ix in if ene==EmptyT then (a:!:b:!:c) else (a:!:b+1:!:c)
  {-# INLINE getParserRange #-}

instance
  ( Elms ls (is:.i)
  ) => Elms (ls :!: DefBtTbl m (is:.i) x b) (is:.i) where
  data Elm (ls :!: DefBtTbl m (is:.i) x b) (is:.i) = ElmBtTbl !(Elm ls (is:.i)) !(x,m (S.Stream m b)) !(is:.i)
  type Arg (ls :!: DefBtTbl m (is:.i) x b) = Arg ls :. (x,m (S.Stream m b))
  getArg !(ElmBtTbl ls x _) = getArg ls :. x
  getIdx !(ElmBtTbl _ _  i) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls (is:.i)
  , ExtShape (is:.i)
  , Shape (is:.i)
  , VU.Unbox x
  , NonTermValidIndex (is:.i)
  , TableIndices (is:.i)
  , MkStream m ls (is:.i)
  ) => MkStream m (ls:!:DefBtTbl m (is:.i) x b) (is:.i) where
  mkStream (ls :!: BtTbl enz tbl f) os is
    = S.map (\(s:!:Z:!:β) -> ElmBtTbl s (tbl PA.! β,f β) β) -- extract data using β index
    . tableIndices os enz is -- generate indices for multiple dimensions
    . S.map (\s -> (s:!:Z:!:getIdx s)) -- extract the right-most current index
    $ mkStream ls (nonTermInnerOuter is os) (nonTermLeftIndex is os enz) -- TODO fix os is!
  {-# INLINE mkStream #-}

instance
  ( ValidIndex ls (is:.i)
  , Shape (is:.i)
  , ExtShape (is:.i)
  , VU.Unbox x
  , NonTermValidIndex (is:.i)
  ) => ValidIndex (ls :!: DefBtTbl m (is:.i) x b) (is:.i) where
  validIndex (ls :!: BtTbl es tbl f) abc isi =
    let (_,rght) = PA.bounds tbl
    in  nonTermValidIndex es rght abc isi && validIndex ls abc isi
  getParserRange (ls :!: BtTbl es _ _) ix = getNonTermParserRange es ix $ getParserRange ls ix
  {-# INLINE validIndex #-}
  {-# INLINE getParserRange #-}



class EmptyTable x where
  toEmptyT :: x -> x
  toNonEmptyT :: x -> x

instance (EmptyENZ (ENZ i)) => EmptyTable (MTbl i xs) where
  toEmptyT    (MTbl enz xs) = MTbl (toEmptyENZ    enz) xs
  toNonEmptyT (MTbl enz xs) = MTbl (toNonEmptyENZ enz) xs
  {-# INLINE toEmptyT #-}
  {-# INLINE toNonEmptyT #-}

instance (EmptyENZ (ENZ i)) => EmptyTable (BtTbl i xs f) where
  toEmptyT    (BtTbl enz xs f) = BtTbl (toEmptyENZ    enz) xs f
  toNonEmptyT (BtTbl enz xs f) = BtTbl (toNonEmptyENZ enz) xs f
  {-# INLINE toEmptyT #-}
  {-# INLINE toNonEmptyT #-}




{-

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




-}




-}

