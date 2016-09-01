
module ADP.Fusion.SynVar.Recursive.Type where

import Control.Applicative (Applicative,(<$>),(<*>))
import Control.Monad.Morph
import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic (Stream,head,map,mapM)
import Prelude hiding (head,map,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi
import ADP.Fusion.SynVar.Axiom
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Indices.Classes
import ADP.Fusion.SynVar.TableWrap



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
  IRec :: { iRecConstraint  :: !c
          , iRecFrom        :: !i
          , iRecTo          :: !i
          } -> IRec c i x

type TwIRec m c i x = TW (IRec c i x) (i -> i -> m x)

type TwIRecBt c i x mF mB r = TW (Backtrack (TwIRec mF c i x) mF mB) (i -> i -> mB [r])

instance Build (TwIRec   m c i x)

instance Build (TwIRecBt c i x mF mB r)

type instance TermArg (TwIRec m c i x) = x

instance GenBacktrackTable (TwIRec mF c i x) mF mB where
  data Backtrack (TwIRec mF c i x) mF mB = BtIRec !c !i !i !(i -> i -> mB x) -- !(i -> i -> mB [r])
  type BacktrackIndex (TwIRec mF c i x) = i
  toBacktrack (TW (IRec c iF iT) f) mrph = BtIRec c iF iT (\lu i -> mrph $ f lu i)
  {-# Inline toBacktrack #-}



instance
  ( Monad m
  , IndexStream i
  ) => Axiom (TwIRec m c i x) where
  type AxiomStream (TwIRec m c i x) = m x
  axiom (TW (IRec _ l h) fun) = do
    k <- head $ streamDown l h
    fun h k
  {-# Inline axiom #-}

instance
  ( Monad mB
  , IndexStream i
  , i ~ j
  , m ~ mB
  ) => Axiom (TW (Backtrack (TwIRec mF c i x) mF mB) (j -> j -> m [r])) where
  type AxiomStream (TW (Backtrack (TwIRec mF c i x) mF mB) (j -> j -> m [r])) = mB [r]
  axiom (TW (BtIRec c l h fun) btfun) = do
    k <- head $ streamDown l h
    btfun h k
  {-# Inline axiom #-}



instance Element ls i => Element (ls :!: TwIRec m c u x) i where
  data Elm (ls :!: TwIRec m c u x) i = ElmIRec !x !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: TwIRec m c u x)   = Arg ls :. x
  getArg (ElmIRec x _ ls) = getArg ls :. x
  getIdx (ElmIRec _ i _ ) = i
  {-# Inline getArg #-}
  {-# Inline getIdx #-}

instance Element ls i => Element (ls :!: TwIRecBt c u x mF mB r) i where
  data Elm (ls :!: (TwIRecBt c u x mF mB r)) i = ElmBtIRec !x [r] !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: (TwIRecBt c u x mF mB r))   = Arg ls :. (x, [r])
  getArg (ElmBtIRec x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtIRec _ _ i _ ) = i
  {-# Inline getArg #-}
  {-# Inline getIdx #-}

instance
  ( Functor m
  , Monad m
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (Elm ls (is:.i)) (us:.u) (cs:.c) (is:.i)
  , MkStream m ls (is:.i)
  ) => MkStream m (ls :!: TwIRec m (cs:.c) (us:.u) x) (is:.i) where
  mkStream (ls :!: TW (IRec c l h) fun) vs us is
    = mapM (\(s,tt,ii) -> (\res -> ElmIRec res ii s) <$> fun h tt)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
  {-# Inline mkStream #-}

instance
  ( Applicative mB
  , Monad mB
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (Elm ls (is:.i)) (us:.u) (cs:.c) (is:.i)
  , MkStream mB ls (is:.i)
  ) => MkStream mB (ls :!: TwIRecBt (cs:.c) (us:.u) x mF mB r) (is:.i) where
  mkStream (ls :!: TW (BtIRec c l h fun) bt) vs us is
    = mapM (\(s,tt,ii) -> (\res bb -> ElmBtIRec res bb ii s) <$> fun h tt <*> bt h tt)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
  {-# Inline mkStream #-}

