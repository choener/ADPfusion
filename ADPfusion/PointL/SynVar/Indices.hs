
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
import Text.Printf

import Data.PrimitiveArray hiding (map)

import ADPfusion.Core
import ADPfusion.Core.SynVar.Indices
import ADPfusion.PointL.Core



-- * type function for the type of the left position

-- ** Inside

type instance LeftPosTy (IStatic '(low,high)) (TwITbl b s m arr EmptyOk (PointL I) x) (PointL I) = IVariable '(low,MaxSz)
type instance LeftPosTy (IStatic '(low,high)) (TwITblBt b s arr EmptyOk (PointL I) x mB mF r) (PointL I) = IVariable '(low,MaxSz)

type instance LeftPosTy (IVariable '(low,high)) (TwITbl b s m arr EmptyOk (PointL I) x) (PointL I) = IVariable '(low,MaxSz)
type instance LeftPosTy (IVariable '(low,high)) (TwITblBt b s arr EmptyOk (PointL I) x mB mF r) (PointL I) = IVariable '(low,MaxSz)

-- ** Outside

type instance LeftPosTy (OStatic '(low,high)) (TwITbl b s m arr EmptyOk (PointL O) x) (PointL O) = OFirstLeft '(low,high)
type instance LeftPosTy (OStatic '(low,high)) (TwITblBt b s arr EmptyOk (PointL O) x mB mF r) (PointL O) = OFirstLeft '(low,high)

type instance LeftPosTy (ORightOf '(low,high)) (TwITbl b s m arr EmptyOk (PointL O) x) (PointL O) = OFirstLeft '(low,high)
type instance LeftPosTy (ORightOf '(low,high)) (TwITblBt b s arr EmptyOk (PointL O) x mB mF r) (PointL O) = OFirstLeft '(low,high)

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
  , MinSize c, KnownNat low
  )
  => AddIndexDense (ps:.IStatic '(low,high)) elm (cs:.c) (us:.PointL I) (is:.PointL I) where
--{{{
  {-# Inline addIndexDenseGo #-}
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.PointL i)
    = map (\(SvS s t y') -> SvS s (t:.PointL (i-low)) (y' :.: RiPlI (i-low)))
    . addIndexDenseGo (Proxy :: Proxy ps) cs ubs us is
    where !low :: Int = fromIntegral . natVal $ Proxy @low
--}}}

instance (AddIndexDenseContext ps elm x0 i0 cs c us (PointL I) is (PointL I), MinSize c, KnownNat low, KnownNat high) =>
  AddIndexDense (ps:.IVariable '(low,high)) elm (cs:.c) (us:.PointL I) (is:.PointL I) where
--{{{
  {-# Inline addIndexDenseGo #-}
  addIndexDenseGo Proxy (cs:.c) (ubs:..ub) (us:..u) (is:.PointL i)
    = flatten mk step . addIndexDenseGo (Proxy @ps) cs ubs us is
    where mk svS = let RiPlI k = getIndex (getIdx $ sS svS) (Proxy :: PRI is (PointL I))
                   in  return $ svS :. max k (i-high)
          -- In @mk@, we have to be careful with calculating @k@ we begin with. There might well be
          -- a "high" size on the rhs, hence we put the index at @max k (i-high)@.
          step (svS@(SvS s t y') :. k)
            | k + csize + low > i = return Done
            | otherwise           = return $ Yield (SvS s (t:.PointL k) (y' :.: RiPlI k)) (svS :. k+1)
          !csize :: Int = minSize c
          !low   :: Int = fromIntegral . natVal $ Proxy @low
          !high  :: Int = fromIntegral . natVal $ Proxy @high
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
--}}}



-- ** Outside

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (PointL O) is (PointL O)
  , MinSize c, KnownNat low, KnownNat high
  ) => AddIndexDense (ps:.OStatic '(low,high)) elm (cs:.c) (us:.PointL O) (is:.PointL O) where
--{{{
  {-# Inline addIndexDenseGo #-}
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..LtPointL u) (is:.PointL i)
    = let !low  :: Int = fromIntegral $ natVal (Proxy @low)
          !high :: Int = fromIntegral $ natVal (Proxy @high)
    in map (\(SvS s t y') -> let RiPlO synvarIx termIx = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
                                 k = synvarIx + low
                             in  -- traceShow (printf "Ix/OStatic @ %d(%d) low/high %d/%d synvarIx %d termIx %d" i u low high synvarIx termIx :: String) $
                                 SvS s (t:.PointL k) (y' :.: RiPlO k termIx) )
    . addIndexDenseGo (Proxy :: Proxy ps) cs ubs us is
--}}}

-- |
--
-- NOTE We need to test for @synvarIx+d>u@ since the @high@ limit might allow moving an index beyond
-- the upper bound.
--
-- TODO this can be improved by counting down and only counting down from the highest possible
-- index!

instance
  ( AddIndexDenseContext ps elm x0 i0 cs c us (PointL O) is (PointL O)
  , MinSize c, KnownNat low, KnownNat high
  ) => AddIndexDense (ps:.ORightOf '(low,high)) elm (cs:.c) (us:.PointL O) (is:.PointL O) where
  {-# Inline addIndexDenseGo #-}
  addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..LtPointL u) (is:.PointL i)
    = let !low = fromIntegral $ natVal (Proxy @low)
          !high = fromIntegral $ natVal (Proxy @high)
          mk svS = return $ svS :. 0
          step (svS@(SvS s t y') :. d)
            | d > high-low || d > u-i = return Done
            | synvarIx+d+low > u = return Done
            | otherwise = -- traceShow (printf "Ix/ORightOf %d(%d) low/high %d/%d synvarix %d termix %d synvartgt %d termtgt %d" i u low high synvarIx termIx synvarTgt termTgt :: String) .
                          return $ Yield (SvS s (t:.PointL synvarTgt) (y' :.: RiPlO synvarTgt termTgt)) (svS:.d+1)
            where RiPlO synvarIx termIx = getIndex (getIdx $ sS svS) (Proxy :: PRI is (PointL O))
                  !synvarTgt = synvarIx + d + low
                  !termTgt = termIx
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
    in flatten mk step . addIndexDenseGo (Proxy :: Proxy ps) cs ubs us is
  --addIndexDenseGo Proxy (cs:._) (ubs:..ub) (us:..u) (is:.i)
  --  = map (\(SvS s t y') → let RiPlO oi oo = getIndex (getIdx s) (Proxy :: PRI is (PointL O))
  --                         in  SvS s (t:.PointL oo) (y' :.: RiPlO oi oo) )
  --  . addIndexDenseGo (Proxy ∷ Proxy ps) cs ubs us is
  --{-# Inline addIndexDenseGo #-}



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

