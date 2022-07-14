
module ADPfusion.Multi.GChr where

import Data.Array.Repa.Index
import Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import Data.Array.Repa.Index.Points
import Data.Array.Repa.Index.Subword

import ADPfusion.Chr
import ADPfusion.Classes
import ADPfusion.Multi.Classes


type instance TermOf (Term ts (GChr r xs)) = TermOf ts :. r



-- * Multi-dim 'Subword's.

-- TODO we want to evaluate @f xs $ j-1@ just once before the stream is
-- generated. Unfortunately, this will evaluate cases like index (-1) as well,
-- which leads to crashes. The code below is safe but slower. We should
-- incorporate a version that performs and @outerCheck@ in the code.

instance
  ( Monad m
  , TermElm m ts is
  ) => TermElm m (Term ts (GChr r xs)) (is:.Subword) where
  termStream (ts :! GChr f xs) (io:.Outer) (is:.ij@(Subword(i:.j)))
    = S.map (\(zs :!: (zix:.kl) :!: zis :!: e) -> (zs :!: zix :!: (zis:.subword (j-1) j) :!: (e:.(f xs $ j-1))))
    . termStream ts io is
    . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  termStream (ts :! GChr f xs) (io:.Inner _ _) (is:.ij)
    = S.map (\(zs :!: (zix:.kl@(Subword(k:.l))) :!: zis :!: e) -> let dta = f xs l in dta `seq` (zs :!: zix :!: (zis:.subword l (l+1)) :!: (e:.dta)))
    . termStream ts io is
    . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  {-# INLINE termStream #-}

instance
  ( TermValidIndex ts is
  ) => TermValidIndex (Term ts (GChr r xs)) (is:.Subword) where
  termDimensionsValid (ts:!GChr _ xs) (prs:.(a:!:b:!:c)) (is:.Subword(i:.j))
    = i>=a && j<=VG.length xs -c && i+b<=j && termDimensionsValid ts prs is
  getTermParserRange (ts:!GChr _ _) (is:._) (prs:.(a:!:b:!:c))
    = getTermParserRange ts is prs :. (a:!:b+1:!:max 0 (c-1))
  termInnerOuter (ts:!_) (is:._) (ios:.io) = termInnerOuter ts is ios :. io
  termLeftIndex  (ts:!_) (is:.Subword (i:.j)) = termLeftIndex ts is :. subword i (j-1)
  {-# INLINE termDimensionsValid #-}
  {-# INLINE getTermParserRange #-}
  {-# INLINE termInnerOuter #-}
  {-# INLINE termLeftIndex #-}



-- * Multi-dim 'PointL's

-- | NOTE This instance is currently the only one using an "inline outer
-- check". If This behaves well, it could be possible to put checks for valid
-- indices inside the outerCheck function. (Currently disabled, as the compiler
-- chokes on four-way alignments).

instance
  ( Monad m
  , TermElm m ts is
  ) => TermElm m (Term ts (GChr r xs)) (is:.PointL) where
  termStream (ts :! GChr f xs) (io:.Outer) (is:.ij@(PointL(i:.j)))
    -- = outerCheck (j>0)
    -- . let dta = (f xs $ j-1) in dta `seq` S.map (\(zs :!: (zix:.kl) :!: zis :!: e) -> (zs :!: zix :!: (zis:.pointL (j-1) j) :!: (e:.dta)))
    = S.map (\(zs :!: (zix:.kl) :!: zis :!: e) -> (zs :!: zix :!: (zis:.pointL (j-1) j) :!: (e:.(f xs $ j-1))))
    . termStream ts io is
    . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  termStream (ts :! GChr f xs) (io:.Inner _ _) (is:.ij)
    = S.map (\(zs :!: (zix:.kl@(PointL(k:.l))) :!: zis :!: e) -> let dta = f xs l in dta `seq` (zs :!: zix :!: (zis:.pointL l (l+1)) :!: (e:.dta)))
    . termStream ts io is
    . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  {-# INLINE termStream #-}

-- TODO auto-generated, check correctness

instance
  ( TermValidIndex ts is
  ) => TermValidIndex (Term ts (GChr r xs)) (is:.PointL) where
  termDimensionsValid (ts:!GChr _ xs) (prs:.(a:!:b:!:c)) (is:.PointL(i:.j))
    = {- i>=a && j<=VG.length xs -c && i+b<=j && -} termDimensionsValid ts prs is
  getTermParserRange (ts:!GChr _ _) (is:._) (prs:.(a:!:b:!:c))
    = getTermParserRange ts is prs :. (a:!:b+1:!:max 0 (c-1))
  termInnerOuter (ts:!_) (is:._) (ios:.io) = termInnerOuter ts is ios :. io
  termLeftIndex  (ts:!_) (is:.PointL (i:.j)) = termLeftIndex ts is :. pointL i (j-1)
  {-# INLINE termDimensionsValid #-}
  {-# INLINE getTermParserRange #-}
  {-# INLINE termInnerOuter #-}
  {-# INLINE termLeftIndex #-}

