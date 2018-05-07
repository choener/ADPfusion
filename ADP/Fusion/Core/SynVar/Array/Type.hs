
{-# Language DataKinds #-}
{-# Language TypeOperators #-}

module ADP.Fusion.Core.SynVar.Array.Type where

import Data.Proxy
import Data.Strict.Tuple hiding (uncurry,snd)
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Debug.Trace
import GHC.TypeNats
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi
import ADP.Fusion.Core.SynVar.Axiom
import ADP.Fusion.Core.SynVar.Backtrack
import ADP.Fusion.Core.SynVar.Indices
import ADP.Fusion.Core.SynVar.TableWrap



-- | Immutable table.
--
-- NOTE / TODO We can *NOT* move the little order into the type-level until we
-- have a fully working TH-based table filler.

data ITbl (bigorder ∷ Nat) {- (littleOrder ∷ Nat) -} arr c i x where
  ITbl ∷ { iTblLittleOrder ∷ Int
         , iTblConstraint  ∷ !c           -- TODO next to go?!
         , iTblArray       ∷ !(arr i x)
         } → ITbl bigOrder arr c i x

instance (Show c, Show (arr i x)) ⇒ Show (ITbl bo arr c i x) where
  show (ITbl lo c arr) = "ITbl " ++ show lo ++ " " ++ show c ++ " [" ++ show arr ++ "]"

type TwITbl b (m ∷ * → *) arr c i x = TW (ITbl b arr c i x) (LimitType i → i → m x)

type TwITblBt b arr c i x mF mB r = TW (Backtrack (TwITbl b mF arr c i x) mF mB) (LimitType i → i → mB [r])

instance Build (TwITbl b m arr c i x)

instance Build (TwITblBt b arr c i x mF mB r)

type instance TermArg (TwITbl b m arr c i x) = x

type instance TermArg (TwITblBt b arr c i x mF mB r) = (x,[r])

instance GenBacktrackTable (TwITbl b mF arr c i x) mF mB where
  data Backtrack (TwITbl b mF arr c i x) mF mB = BtITbl !c !(arr i x)
  type BacktrackIndex (TwITbl b mF arr c i x) = i
  toBacktrack (TW (ITbl _ c arr) _) _ = BtITbl c arr
  {-# Inline toBacktrack #-}



-- * axiom stuff

instance
  ( Monad m
  , PrimArrayOps arr i x
  , IndexStream i
  ) ⇒ Axiom (TwITbl b m arr c i x) where
  type AxiomStream (TwITbl b m arr c i x) = m x
  axiom (TW (ITbl _ c arr) _) = do
    k ← head . streamDown zeroBound' $ upperBound arr
    return $ arr ! k
  {-# Inline axiom #-}

-- | We need this somewhat annoying instance construction (@i ~ j@ and @m
-- ~ mB@) in order to force selection of this instance.

instance
  ( Monad mB
  , PrimArrayOps arr i x
  , IndexStream i
  , j ~ i
  , m ~ mB
  ) ⇒ Axiom (TW (Backtrack (TwITbl b mF arr c i x) mF mB) (LimitType j → j → m [r])) where
  type AxiomStream (TW (Backtrack (TwITbl b mF arr c i x) mF mB) (LimitType j → j → m [r])) = mB [r]
  axiom (TW (BtITbl c arr) bt) = do
    h ← head . streamDown zeroBound' $ upperBound arr
    bt (upperBound arr) h
  {-# Inline axiom #-}



-- * 'Element'

instance Element ls i ⇒ Element (ls :!: TwITbl b m arr c j x) i where
  data Elm    (ls :!: TwITbl b m arr c j x) i = ElmITbl !x !(RunningIndex i) !(Elm ls i)
  type Arg    (ls :!: TwITbl b m arr c j x)   = Arg ls :. x
  type RecElm (ls :!: TwITbl b m arr c j x) i = Elm ls i
  getArg (ElmITbl x _ ls) = getArg ls :. x
  getIdx (ElmITbl _ i _ ) = i
  getElm (ElmITbl _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i), Show x) => Show (Elm (ls :!: TwITbl b m arr c j x) i)

instance Element ls i => Element (ls :!: TwITblBt b arr c j x mF mB r) i where
  data Elm    (ls :!: TwITblBt b arr c j x mF mB r) i = ElmBtITbl !x [r] !(RunningIndex i) !(Elm ls i)
  type Arg    (ls :!: TwITblBt b arr c j x mF mB r)   = Arg ls :. (x, [r])
  type RecElm (ls :!: TwITblBt b arr c j x mF mB r) i = Elm ls i
  getArg (ElmBtITbl x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtITbl _ _ i _ ) = i
  getElm (ElmBtITbl _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

instance (Show x, Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: TwITblBt b arr c i x mF mB r) i) where
  show (ElmBtITbl x _ i s) = show (x,i) ++ " " ++ show s



-- * Multi-dim extensions

type instance LeftPosTy Z (TwITbl b m arr EmptyOk Z x) Z = Z
type instance LeftPosTy Z (TwITblBt b arr EmptyOk Z x mF mB r) Z = Z

type instance LeftPosTy (ps:.p) (TwITbl b m arr (eos:.EmptyOk) (us:.u) x) (is:.i)
  = (LeftPosTy ps (TwITbl b m arr eos us x) is) :. (LeftPosTy p (TwITbl b m arr EmptyOk u x) i)

type instance LeftPosTy (ps:.p) (TwITblBt b arr (eos:.EmptyOk) (us:.u) x mF mB r) (is:.i)
  = (LeftPosTy ps (TwITblBt b arr eos us x mF mB r) is) :. (LeftPosTy p (TwITblBt b arr EmptyOk u x mF mB r) i)

type instance LeftPosTy Z (TwITbl b m arr Z Z x) Z = Z
type instance LeftPosTy Z (TwITblBt b arr Z Z x mF mB r) Z = Z


instance
  forall b l m pos ps p posLeft arr cs c us u x is i ls
  . ( Monad m
  , pos ~ (ps:.p)
  , posLeft ~ LeftPosTy pos (TwITbl b m arr (cs:.c) (us:.u) x) (is:.i)
  , Element ls (is:.i)
  , TableStaticVar (ps:.p) (cs:.c) (us:.u) (is:.i)
  , AddIndexDense pos (Elm ls (is:.i)) (cs:.c) (us:.u) (is:.i)
  , MkStream m posLeft ls (is:.i)
  , PrimArrayOps arr (us:.u) x
  ) ⇒ MkStream m (ps:.p) (ls :!: TwITbl b m arr (cs:.c) (us:.u) x) (is:.i) where
  mkStream Proxy (ls :!: TW (ITbl _ csc t) _) grd usu isi
    = map (\(s,tt,ii') -> ElmITbl (t!tt) ii' s)
    . addIndexDense (Proxy ∷ Proxy pos) csc ub usu isi
    $ mkStream (Proxy ∷ Proxy posLeft) ls grd usu (tableStreamIndex (Proxy ∷ Proxy pos) csc ub isi)
    where ub = upperBound t
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , pos ~ (ps:.p)
  , posLeft ~ LeftPosTy pos (TwITblBt b arr (cs:.c) (us:.u) x mF mB r) (is:.i)
  , Element ls (is:.i)
  , TableStaticVar (ps:.p) (cs:.c) (us:.u) (is:.i)
  , AddIndexDense pos (Elm ls (is:.i)) (cs:.c) (us:.u) (is:.i)
  , MkStream mB posLeft ls (is:.i)
  , PrimArrayOps arr (us:.u) x
  ) ⇒ MkStream mB (ps:.p) (ls :!: TwITblBt b arr (cs:.c) (us:.u) x mF mB r) (is:.i) where
  mkStream Proxy (ls :!: TW (BtITbl csc t) bt) grd usu isi
    = mapM (\(s,tt,ii') -> bt ub tt >>= \ ~bb -> return $ ElmBtITbl (t!tt) bb ii' s)
    . addIndexDense (Proxy ∷ Proxy pos) csc ub usu isi
    $ mkStream (Proxy ∷ Proxy posLeft) ls grd usu (tableStreamIndex (Proxy :: Proxy pos) csc ub isi)
    where ub = upperBound t
  {-# Inline mkStream #-}

