
module ADPfusion.Multi.None where

import Data.Array.Repa.Index
import Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import Data.Array.Repa.Index.Points

import ADPfusion.Classes
import ADPfusion.Multi.Classes
import ADPfusion.None



type instance TermOf (Term ts None) = TermOf ts :. ()

instance
  ( Monad m
  , TermElm m ts is
  ) => TermElm m (Term ts None) (is:.PointL) where
  termStream (ts :! None) (io:.Outer) (is:.ij@(PointL(i:.j))) =
    S.map (\(zs :!: (zix:.kl) :!: zis :!: e) -> (zs :!: zix :!: (zis:.kl) :!: (e:.())))
    . termStream ts io is
    . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  termStream (ts :! None) (io:.Inner _ _) (is:.ij)
    = S.map (\(zs :!: (zix:.kl) :!: zis :!: e) -> (zs :!: zix :!: (zis:.kl) :!: (e:.())))
    . termStream ts io is
    . S.map (\(zs :!: zix :!: (zis:.kl)) -> (zs :!: (zix:.kl) :!: zis))
  {-# INLINE termStream #-}

-- TODO auto-gen'ed

instance
  ( TermValidIndex ts is
  ) => TermValidIndex (Term ts None) (is:.PointL) where
  termDimensionsValid (ts:!None) (prs:.(a:!:b:!:c)) (is:.PointL(i:.j))
    = termDimensionsValid ts prs is
  getTermParserRange (ts:!None) (is:._) (prs:.(a:!:b:!:c))
    = getTermParserRange ts is prs :. (a:!:b:!:c)
  termInnerOuter (ts:!_) (is:._) (ios:.io) = termInnerOuter ts is ios :. io
  termLeftIndex  (ts:!_) (is:.ij) = termLeftIndex ts is :. ij
  {-# INLINE termDimensionsValid #-}
  {-# INLINE getTermParserRange #-}
  {-# INLINE termInnerOuter #-}
  {-# INLINE termLeftIndex #-}

