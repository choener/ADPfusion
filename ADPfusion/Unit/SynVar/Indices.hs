
-- | TODO if we have a table that has min-size @>0@ we need to immediately
-- terminate @addIndexDenseGo@ !

module ADPfusion.Unit.SynVar.Indices where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADPfusion.Core
import ADPfusion.Unit.Core



type instance LeftPosTy (IStatic d) (TwITbl b s m arr EmptyOk (Unit I) x) (Unit I) = IStatic d
type instance LeftPosTy (IStatic d) (TwITblBt b s arr EmptyOk (Unit I) x mB mF r) (Unit I) = IStatic d

type instance LeftPosTy (OStatic d) (TwITbl b s m arr EmptyOk (Unit O) x) (Unit O) = OStatic d
type instance LeftPosTy (OStatic d) (TwITblBt b s arr EmptyOk (Unit O) x mB mF r) (Unit O) = OStatic d

type instance LeftPosTy Complement (TwITbl b s m arr EmptyOk (Unit I) x) (Unit C) = Complement
type instance LeftPosTy Complement (TwITblBt b s arr EmptyOk (Unit I) x mB mF r) (Unit C) = Complement

type instance LeftPosTy Complement (TwITbl b s m arr EmptyOk (Unit O) x) (Unit C) = Complement
type instance LeftPosTy Complement (TwITblBt b s arr EmptyOk (Unit O) x mB mF r) (Unit C) = Complement

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (Unit I) is (Unit I)
  , MinSize c
  )
  ⇒ AddIndexDense (ps:.Unit d) elm (cs:.c) (us:.Unit I) (is:.Unit I) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y') → SvS s (t:.i) (y' :.: RiUnit))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (Unit O) is (Unit O)
  , MinSize c
  )
  ⇒ AddIndexDense (ps:.Unit d) elm (cs:.c) (us:.Unit O) (is:.Unit O) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y') → SvS s (t:.i) (y' :.: RiUnit))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (Unit I) is (Unit C)
  , MinSize c
  )
  ⇒ AddIndexDense (ps:.Unit d) elm (cs:.c) (us:.Unit I) (is:.Unit C) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y') → SvS s (t:.Unit) (y' :.: RiUnit))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (Unit O) is (Unit C)
  , MinSize c
  )
  ⇒ AddIndexDense (ps:.Unit d) elm (cs:.c) (us:.Unit O) (is:.Unit C) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y') → SvS s (t:.Unit) (y' :.: RiUnit))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

