
-- | Index movement for syntactic variables in linear @PointL@ grammars.
--
-- Syntactic variables for @PointL@ indices can be both, static and variable.
-- Static is the default, whenever we have @X -> X a@ where @a@ is a character
-- or similar. However, we can expect to see @a@ as a string as well. Then, @X@
-- on the r.h.s. is variable.

module ADPfusion.PointR.SynVar.Indices where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..),flatten)
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADPfusion.Core
import ADPfusion.Core.SynVar.Indices
import ADPfusion.PointR.Core



type instance LeftPosTy (IStatic d) (TwITbl b s m arr EmptyOk (PointR I) x) (PointR I) = IVariable d
type instance LeftPosTy (IStatic d) (TwITblBt b s arr EmptyOk (PointR I) x mB mF r) (PointR I) = IVariable d

type instance LeftPosTy (IVariable d) (TwITbl b s m arr EmptyOk (PointR I) x) (PointR I) = IVariable d
type instance LeftPosTy (IVariable d) (TwITblBt b s arr EmptyOk (PointR I) x mB mF r) (PointR I) = IVariable d



instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (PointR I) is (PointR I)
  , MinSize c
  )
  ⇒ AddIndexDense (ps:.IStatic d) elm (cs:.c) (us:.PointR I) (is:.PointR I) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..LtPointR u) (is:.i)
    = map (\(SvS s t y') →
        let RiPrI k = getIndex (getIdx s) (Proxy ∷ PRI is (PointR I))
        in  SvS s (t:.PointR k) (y' :.: RiPrI  u))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

