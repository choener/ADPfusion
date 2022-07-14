
-- | Index movement for syntactic variables in linear @PointL@ grammars.
--
-- Syntactic variables for @PointL@ indices can be both, static and variable.
-- Static is the default, whenever we have @X -> X a@ where @a@ is a character
-- or similar. However, we can expect to see @a@ as a string as well. Then, @X@
-- on the r.h.s. is variable.

module ADPfusion.PointL.SynVar.Indices where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..),flatten)
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADPfusion.Core
import ADPfusion.Core.SynVar.Indices
import ADPfusion.PointL.Core



-- * type function for the type of the left position

-- ** Inside

type instance LeftPosTy (IStatic d) (TwITbl b s m arr EmptyOk (PointL I) x) (PointL I) = IVariable d
type instance LeftPosTy (IStatic d) (TwITblBt b s arr EmptyOk (PointL I) x mB mF r) (PointL I) = IVariable d

type instance LeftPosTy (IVariable d) (TwITbl b s m arr EmptyOk (PointL I) x) (PointL I) = IVariable d
type instance LeftPosTy (IVariable d) (TwITblBt b s arr EmptyOk (PointL I) x mB mF r) (PointL I) = IVariable d

-- ** Outside

type instance LeftPosTy (OStatic d) (TwITbl b s m arr EmptyOk (PointL O) x) (PointL O) = OFirstLeft d
type instance LeftPosTy (OStatic d) (TwITblBt b s arr EmptyOk (PointL O) x mB mF r) (PointL O) = OFirstLeft d

-- TODO @OLeftOf@

type instance LeftPosTy (OFirstLeft d) (TwITbl b s m arr EmptyOk (PointL O) x) (PointL O) = TypeError
  (Text "OFirstLeft is illegal for outside tables. Check your grammars for multiple Outside syntactic variable on the r.h.s!")
type instance LeftPosTy (OFirstLeft d) (TwITblBt b s arr EmptyOk (PointL O) x mB mF r) (PointL O) = TypeError
  (Text "OFirstLeft is illegal for outside tables. Check your grammars for multiple Outside syntactic variable on the r.h.s!")

type instance LeftPosTy (OLeftOf d) (TwITbl b s m arr EmptyOk (PointL O) x) (PointL O) = TypeError
  (Text "OLeftOf is illegal for outside tables. Check your grammars for multiple Outside syntactic variable on the r.h.s!")
type instance LeftPosTy (OLeftOf d) (TwITblBt s b arr EmptyOk (PointL O) x mB mF r) (PointL O) = TypeError
  (Text "OLeftOf is illegal for outside tables. Check your grammars for multiple Outside syntactic variable on the r.h.s!")

-- ** Complement. Note that @Complement@ joins inside and outside syntactic
-- variables.

type instance LeftPosTy Complement (TwITbl b s m arr EmptyOk (PointL I) x) (PointL C) = Complement
type instance LeftPosTy Complement (TwITblBt b s arr EmptyOk (PointL I) x mB mF r) (PointL C) = Complement

type instance LeftPosTy Complement (TwITbl b s m arr EmptyOk (PointL O) x) (PointL C) = Complement
type instance LeftPosTy Complement (TwITblBt b s arr EmptyOk (PointL O) x mB mF r) (PointL C) = Complement



-- * 'AddIndexDense' instances

-- ** Inside

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (PointL I) is (PointL I)
  , MinSize c
  )
  ⇒ AddIndexDense (ps:.IStatic d) elm (cs:.c) (us:.PointL I) (is:.PointL I) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y') → SvS s (t:.i) (y' :.: RiPlI (fromPointL i)))
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (PointL I) is (PointL I)
  , MinSize c
  )
  ⇒ AddIndexDense (ps:.IVariable d) elm (cs:.c) (us:.PointL I) (is:.PointL I) where
  addIndexDenseGo Proxy (cs:.c) (ubs:..ub) (us:..u) (is:.PointL i)
    = flatten mk step . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
    where mk svS = let RiPlI k = getIndex (getIdx $ sS svS {- sIx svS -} ) (Proxy :: PRI is (PointL I))
                   in  return $ svS :. k
          step (svS@(SvS s t y') :. k)
            | k + csize > i = return $ Done
            | otherwise     = return $ Yield (SvS s (t:.PointL k) (y' :.: RiPlI k)) (svS :. k+1)
            where csize = minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}



-- ** Outside

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (PointL O) is (PointL O)
  , MinSize c
  ) ⇒ AddIndexDense (ps:.OStatic d) elm (cs:.c) (us:.PointL O) (is:.PointL O) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y') → let RiPlO oi oo = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                           in  SvS s (t:.PointL oo) (y' :.: RiPlO oi oo) )
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (PointL O) is (PointL O)
  , MinSize c
  ) ⇒ AddIndexDense (ps:.ORightOf d) elm (cs:.c) (us:.PointL O) (is:.PointL O) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y') → let RiPlO oi oo = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                           in  SvS s (t:.PointL oo) (y' :.: RiPlO oi oo) )
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}



-- ** Complement

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (PointL I) is (PointL C)
  ) ⇒ AddIndexDense (ps:.Complement) elm (cs:.c) (us:.PointL I) (is:.PointL C) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y) → let RiPlC k = getIndex (getIdx s) (Proxy :: PRI is (PointL C))
                          in  SvS s (t:.PointL k) (y :.: RiPlC k) )
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (PointL O) is (PointL C)
  ) ⇒ AddIndexDense (ps:.Complement) elm (cs:.c) (us:.PointL O) (is:.PointL C) where
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
    = map (\(SvS s t y) → let RiPlC k = getIndex (getIdx s) (Proxy :: PRI is (PointL C))
                          in  SvS s (t:.PointL k) (y:.:RiPlC k) )
    . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  {-# Inline addIndexDenseGo #-}

