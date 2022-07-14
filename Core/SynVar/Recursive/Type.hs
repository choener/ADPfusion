
module ADPfusion.Core.SynVar.Recursive.Type where

import Control.Applicative (Applicative,(<$>),(<*>))
import Control.Monad.Morph
import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic (Stream,head,map,mapM)
import Prelude hiding (head,map,mapM)

import Data.PrimitiveArray hiding (map)

import ADPfusion.Core.Classes
import ADPfusion.Core.Multi
import ADPfusion.Core.SynVar.Axiom
import ADPfusion.Core.SynVar.Backtrack
import ADPfusion.Core.SynVar.Indices
import ADPfusion.Core.SynVar.TableWrap



-- | A syntactic variable that does not memoize but simplify recurses. One
-- needs to be somewhat careful when using this one. @ITbl@ performs
-- memoization to perform DP in polynomial time (roughly speaking). If the
-- rules for an @IRec@ are of a particular type, they will exponential
-- running time. Things like @X -> X X@ are, for example, rather bad. Rules
-- of the type @X -> Y, Y -> Z@ are ok, if @Y@ is an @IRec@ since we just
-- continue on. The same holds for @Y -> a Y@. Basically, things are safe
-- if there is only a (small) constant number of parses of an @IRec@
-- synvar.

data IRec c i x where
  IRec ∷ { iRecConstraint ∷ !c
         , iRecTo         ∷ !(LimitType i)
         } -> IRec c i x

type TwIRec (m ∷ * -> *) c i x = TW (IRec c i x) (LimitType i -> i -> m x)

type TwIRecBt c i x mF mB r = TW (Backtrack (TwIRec mF c i x) mF mB) (LimitType i -> i -> mB [r])

instance Build (TwIRec   m c i x)

instance Build (TwIRecBt c i x mF mB r)

type instance TermArg (TwIRec m c i x) = x

instance GenBacktrackTable (TwIRec mF c i x) mF mB where
  data Backtrack (TwIRec mF c i x) mF mB = BtIRec !c !(LimitType i) !(LimitType i -> i -> mB x)
  type BacktrackIndex (TwIRec mF c i x) = i
  toBacktrack (TW (IRec c iT) f) mrph = BtIRec c iT (\lu i -> mrph $ f lu i)
  {-# Inline toBacktrack #-}



instance
  ( Monad m
  , IndexStream i
  ) => Axiom (TwIRec m c i x) where
  type AxiomStream (TwIRec m c i x) = m x
  type AxiomIx     (TwIRec m c i x) = i
  {-# Inline axiom #-}
  axiom (TW (IRec _ h) fun) = do
    k ← head $ streamDown zeroBound' h
    fun h k
  {-# Inline axiomAt #-}
  axiomAt (TW (IRec _ h) fun) k = fun h k

instance
  ( Monad mB
  , IndexStream i
  , i ~ j
  , m ~ mB
  ) => Axiom (TW (Backtrack (TwIRec mF c i x) mF mB) (LimitType j -> j -> m [r])) where
  type AxiomStream (TW (Backtrack (TwIRec mF c i x) mF mB) (LimitType j -> j -> m [r])) = mB [r]
  type AxiomIx     (TW (Backtrack (TwIRec mF c i x) mF mB) (LimitType j -> j -> m [r])) = i
  axiom (TW (BtIRec c h fun) btfun) = do
    k <- head $ streamDown zeroBound' h
    btfun h k
  {-# Inline axiom #-}
  axiomAt (TW (BtIRec c h fun) btfun) k = btfun h k
  {-# Inline axiomAt #-}



instance Element ls i => Element (ls :!: TwIRec m c u x) i where
  data Elm (ls :!: TwIRec m c u x) i = ElmIRec !x !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: TwIRec m c u x)   = Arg ls :. x
  type RecElm (ls :!: TwIRec m c u x) i = Elm (ls :!: TwIRec m c u x) i
  getArg (ElmIRec x _ ls) = getArg ls :. x
  getIdx (ElmIRec _ i _ ) = i
  getElm = id
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

instance Element ls i => Element (ls :!: TwIRecBt c u x mF mB r) i where
  data Elm (ls :!: (TwIRecBt c u x mF mB r)) i = ElmBtIRec !x [r] !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: (TwIRecBt c u x mF mB r))   = Arg ls :. (x, [r])
  type RecElm (ls :!: (TwIRecBt c u x mF mB r)) i = Elm (ls :!: (TwIRecBt c u x mF mB r)) i
  getArg (ElmBtIRec x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtIRec _ _ i _ ) = i
  getElm = id
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getElm #-}

instance
  ( Functor m
  , Monad m
  , pos ~ (ps:.p)
  , posLeft ~ LeftPosTy pos (TwIRec m (cs:.c) (us:.u) x) (is:.i)
  , Element ls (is:.i)
--  , TableStaticVar ps cs us is
--  , TableStaticVar p  c  u  i
  , TableStaticVar (ps:.p) (cs:.c) (us:.u) (is:.i)
  , AddIndexDense pos (Elm ls (is:.i)) (cs:.c) (us:.u) (is:.i)
  , MkStream m posLeft ls (is:.i)
  ) => MkStream m ('(:.) ps p) (ls :!: TwIRec m (cs:.c) (us:.u) x) (is:.i) where
  mkStream Proxy (ls :!: TW (IRec csc h) fun) grd usu isi
    = mapM (\(s,tt,ii) -> (\res -> ElmIRec res ii s) <$> fun h tt)
    . addIndexDense (Proxy ∷ Proxy pos) csc h usu isi
    $ mkStream (Proxy ∷ Proxy posLeft) ls grd usu (tableStreamIndex (Proxy ∷ Proxy pos) csc h isi)
  {-# Inline mkStream #-}

instance
  ( Applicative mB
  , Monad mB
  , pos ~ (ps :. p)
  , posLeft ~ LeftPosTy pos (TwIRecBt (cs:.c) (us:.u) x mF mB r) (is:.i)
  , Element ls (is:.i)
--  , TableStaticVar (us:.u) (cs:.c) (is:.i)
--  , TableStaticVar ps cs us is
--  , TableStaticVar p  c  u  i
  , TableStaticVar (ps:.p) (cs:.c) (us:.u) (is:.i)
  , AddIndexDense pos (Elm ls (is:.i)) (cs:.c) (us:.u) (is:.i)
  , MkStream mB posLeft ls (is:.i)
  ) => MkStream mB  ('(:.) ps p) (ls :!: TwIRecBt (cs:.c) (us:.u) x mF mB r) (is:.i) where
  mkStream Proxy (ls :!: TW (BtIRec csc h fun) bt) grd usu isi
    = mapM (\(s,tt,ii) -> (\res bb -> ElmBtIRec res bb ii s) <$> fun h tt <*> bt h tt)
    . addIndexDense (Proxy ∷ Proxy pos) csc h usu isi
    $ mkStream (Proxy ∷ Proxy posLeft) ls grd usu (tableStreamIndex (Proxy :: Proxy pos) csc h isi)
  {-# Inline mkStream #-}

