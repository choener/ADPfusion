{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | The multi-tape extension of ADPfusion.

module ADP.Fusion.Multi where

import Data.Array.Repa.Index
import Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Unboxed as VU

import Data.Array.Repa.Index.Subword
import Data.Array.Repa.Index.Point
import Data.Array.Repa.Index.Points

import ADP.Fusion.Classes
import ADP.Fusion.Chr (GChr (..))

import Debug.Trace

-- import Data.Array.Repa.Index.Subword



{-
data Term a b where
  T    :: Term a b
  (:!) :: !(Term a b) -> !c -> Term (Term a b) c
-}

data TermBase = T

data Term a b = a :! b

instance Build (Term a b)

instance
  ( ValidIndex ls ix
  , TermValidIndex (Term a b) ix
  , Show ix
  , Show (ParserRange ix)
  ) => ValidIndex (ls :!: Term a b) ix where
  validIndex (ls :!: t) abc ix =
    termDimensionsValid t abc ix && validIndex ls abc ix
  {-# INLINE validIndex #-}
  getParserRange (ls :!: t) ix = getTermParserRange t ix (getParserRange ls ix)
  {-# INLINE getParserRange #-}

instance
  ( Elms ls ix
  ) => Elms (ls :!: Term a b) ix where
    data Elm (ls :!: Term a b) ix = ElmTerm !(Elm ls ix) !(TermOf (Term a b)) !ix
    type Arg (ls :!: Term a b) = Arg ls :. (TermOf (Term a b))
    getArg !(ElmTerm ls x _) = getArg ls :. x
    getIdx !(ElmTerm _ _ idx) = idx
    {-# INLINE getArg #-}
    {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls ix
  , MkStream m ls ix
  , TermElm m (Term a b) ix
  , TermValidIndex (Term a b) ix
  ) => MkStream m (ls :!: Term a b) ix where
  mkStream !(ls :!: t) !io !ij
    = S.map (\(s:!:Z:!:zij:!:e) -> ElmTerm s e zij)
    $ termStream t io ij
    $ S.map (\s -> (s :!: Z :!: getIdx s))
    $ mkStream ls (termInnerOuter t ij io) (termLeftIndex t ij)
  {-# INLINE mkStream #-}

class
  ( Monad m
  ) => TermElm m t ix where
  termStream :: t -> InOut ix -> ix -> S.Stream m (ze :!: zix :!: ix) -> S.Stream m (ze :!: zix :!: ix :!: TermOf t)

type family TermOf t :: *

type instance TermOf (Term ts (GChr r xs)) = TermOf ts :. r

instance
  ( Monad m
  , TermElm m ts is
  ) => TermElm m (Term ts (GChr r xs)) (is:.Subword) where
  termStream (ts :! GChr f xs) (io:.Outer) (is:.ij@(Subword(i:.j))) =
    let dta = f xs (j-1)
    in  dta `seq` S.map (\(zs :!: (zix:.kl) :!: zis :!: e) -> (zs :!: zix :!: (zis:.subword (j-1) j) :!: (e:.dta)))
        . termStream ts io is
        . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  termStream (ts :! GChr f xs) (io:.Inner _ _) (is:.ij)
    = S.map (\(zs :!: (zix:.kl@(Subword(k:.l))) :!: zis :!: e) -> let dta = f xs l in dta `seq` (zs :!: zix :!: (zis:.subword l (l+1)) :!: (e:.dta)))
    . termStream ts io is
    . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  {-# INLINE termStream #-}

-- TODO auto-generated, check correctness

instance
  ( Monad m
  , TermElm m ts is
  ) => TermElm m (Term ts (GChr r xs)) (is:.PointL) where
  termStream (ts :! GChr f xs) (io:.Outer) (is:.ij@(PointL(i:.j))) =
    let dta = f xs (j-1)
    in  dta `seq` S.map (\(zs :!: (zix:.kl) :!: zis :!: e) -> (zs :!: zix :!: (zis:.pointL (j-1) j) :!: (e:.dta)))
        . termStream ts io is
        . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  termStream (ts :! GChr f xs) (io:.Inner _ _) (is:.ij)
    = S.map (\(zs :!: (zix:.kl@(PointL(k:.l))) :!: zis :!: e) -> let dta = f xs l in dta `seq` (zs :!: zix :!: (zis:.pointL l (l+1)) :!: (e:.dta)))
    . termStream ts io is
    . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  {-# INLINE termStream #-}

type instance TermOf TermBase = Z

instance
  ( Monad m
  ) => TermElm m (TermBase) Z where
  termStream T _ Z = S.map (\(zs:!:zix:!:Z) -> (zs:!:zix:!:Z:!:Z))
  {-# INLINE termStream #-}

class TermValidIndex t i where
  termDimensionsValid :: t -> ParserRange i -> i -> Bool
  getTermParserRange  :: t -> i -> ParserRange i -> ParserRange i
  termInnerOuter :: t -> i -> InOut i -> InOut i
  termLeftIndex :: t -> i -> i

instance TermValidIndex TermBase Z where
  termDimensionsValid T Z Z = True
  getTermParserRange  T Z Z = Z
  termInnerOuter T Z Z = Z
  termLeftIndex T Z = Z
  {-# INLINE termDimensionsValid #-}
  {-# INLINE getTermParserRange #-}
  {-# INLINE termInnerOuter #-}
  {-# INLINE termLeftIndex #-}

instance
  ( TermValidIndex ts is
  , VU.Unbox xs
  ) => TermValidIndex (Term ts (GChr r xs)) (is:.Subword) where
  termDimensionsValid (ts:!GChr _ xs) (prs:.(a:!:b:!:c)) (is:.Subword(i:.j))
    = i>=a && j<=VU.length xs -c && i+b<=j && termDimensionsValid ts prs is
  getTermParserRange (ts:!GChr _ _) (is:._) (prs:.(a:!:b:!:c))
    = getTermParserRange ts is prs :. (a:!:b+1:!:max 0 (c-1))
  termInnerOuter (ts:!_) (is:._) (ios:.io) = termInnerOuter ts is ios :. io
  termLeftIndex  (ts:!_) (is:.Subword (i:.j)) = termLeftIndex ts is :. subword i (j-1)
  {-# INLINE termDimensionsValid #-}
  {-# INLINE getTermParserRange #-}
  {-# INLINE termInnerOuter #-}
  {-# INLINE termLeftIndex #-}

-- TODO auto-generated, check correctness

instance
  ( TermValidIndex ts is
  , VU.Unbox xs
  ) => TermValidIndex (Term ts (GChr r xs)) (is:.PointL) where
  termDimensionsValid (ts:!GChr _ xs) (prs:.(a:!:b:!:c)) (is:.PointL(i:.j))
    = i>=a && j<=VU.length xs -c && i+b<=j && termDimensionsValid ts prs is
  getTermParserRange (ts:!GChr _ _) (is:._) (prs:.(a:!:b:!:c))
    = getTermParserRange ts is prs :. (a:!:b+1:!:max 0 (c-1))
  termInnerOuter (ts:!_) (is:._) (ios:.io) = termInnerOuter ts is ios :. io
  termLeftIndex  (ts:!_) (is:.PointL (i:.j)) = termLeftIndex ts is :. pointL i (j-1)
  {-# INLINE termDimensionsValid #-}
  {-# INLINE getTermParserRange #-}
  {-# INLINE termInnerOuter #-}
  {-# INLINE termLeftIndex #-}









