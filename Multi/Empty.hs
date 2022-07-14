
module ADPfusion.Multi.Empty where

import Data.Array.Repa.Index
import Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import Data.Array.Repa.Index.Points

import ADPfusion.Classes
import ADPfusion.Empty
import ADPfusion.Multi.Classes



type instance TermOf (Term ts Empty) = TermOf ts :. ()

-- ** @PointL@ instances

instance
  ( Monad m
  , TermElm m ts is
  ) => TermElm m (Term ts Empty) (is:.PointL) where
  termStream (ts:!Empty) (io:.Outer) (is:.ij@(PointL(i:.j))) =
    S.map (\(zs:!:(zix:.kl):!:zis:!:e) -> (zs:!:zix:!:(zis:.kl):!:(e:.())))
    . S.filter (const (i==j))
    . termStream ts io is
    . S.map (\(zs:!:zix:!:(zis:.kl)) -> (zs:!:(zix:.kl):!:zis))
  {-# INLINE termStream #-}

instance
  ( TermValidIndex ts is
  ) => TermValidIndex (Term ts Empty) (is:.PointL) where
  termDimensionsValid (ts:!Empty) (prs:.(a:!:b:!:c)) (is:.PointL(i:.j))
    = termDimensionsValid ts prs is
  getTermParserRange (ts:!Empty) (is:._) (prs:.(a:!:b:!:c))
    = getTermParserRange ts is prs :. (a:!:b:!:c)
  termInnerOuter (ts:!_) (is:._) (ios:.io) = termInnerOuter ts is ios :. io
  termLeftIndex  (ts:!_) (is:.ij) = termLeftIndex ts is :. ij
  {-# INLINE termDimensionsValid #-}
  {-# INLINE getTermParserRange #-}
  {-# INLINE termInnerOuter #-}
  {-# INLINE termLeftIndex #-}

-- ** @Subword@ instances

instance
    ( Monad m
    , TermElm m ts is
    ) => TermElm m (Term ts Empty) (is:.Subword) where

instance
    ( TermValidIndex ts is
    ) => TermValidIndex (Term ts Empty) (is:.Subword) where


