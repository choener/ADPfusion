
module ADP.Fusion.SynVar.Recursive.Type where

import Control.Monad.Morph
import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic (Stream,head,map,mapM)
import Prelude hiding (head,map,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Axiom
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Indices
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
--
-- TODO the @x@ is superfluous now?

data IRec c i where
  IRec :: { iRecConstraint  :: !c
          , iRecFrom        :: !i
          , iRecTo          :: !i
          } -> IRec c i

type TwIRec m c i x = TW m (IRec c i) x -- (IRec c i x) (i -> i -> m x)

instance MkTW m (IRec c i) x where
  data TW m (IRec c i) x =
    TwIRec
      { twIRecStruc :: IRec c i
      , twIRecFun :: i -> i -> m x
      }
  type TWTblTy m (IRec c i) x = IRec c i
  type TWFunTy m (IRec c i) x = i -> i -> m x
  tw = TwIRec
  {-# Inline tw #-}

type TwIRecBt mB mF c i x r = TW mB (Backtrack (TW mF (IRec c i) x)) r

-- |
--
-- TODO the function @m' x -> m x@ should maybe just be from a type class

instance MkTW m (Backtrack (TW m' (IRec c i) x)) r where
  data TW m (Backtrack (TW m' (IRec c i) x)) r =
    TwIRecBt
      { twIRecBtStruc :: !(IRec c i)
      , twIRecBtFwd :: i -> i -> m' x
      , twIRecBtFun :: i -> i -> m [r]
      , twIRecMrph  :: m' x -> m x
      }
  type TWTblTy m (Backtrack (TW m' (IRec c i) x)) r = (TwIRec m' c i x, m' x -> m x)
  type TWFunTy m (Backtrack (TW m' (IRec c i) x)) r = i -> i -> m [r]
  tw = \(TwIRec s fwd, mrph) bt -> TwIRecBt s fwd bt mrph
  {-# Inline tw #-}

instance Build (TwIRec m c i x)

instance Build (TwIRecBt mB mF c i x r)

type instance TermArg (TwIRec m c i x) = x

type instance TermArg (TwIRecBt mB mF c i x r) = (x,[r])



instance
  ( Monad m
  , IndexStream i
  ) => Axiom (TwIRec m c i x) where
  type AxiomStream (TwIRec m c i x) = m x
  axiom (TwIRec (IRec _ l h) fun) = do
    k <- head $ streamDown l h
    fun h k
  {-# Inline axiom #-}

instance
  ( Monad mB
  , IndexStream i
--  , i ~ j
--  , m ~ mB
  ) => Axiom (TwIRecBt mB mF c i x r) where
  type AxiomStream (TwIRecBt mB mF c i x r) = mB [r]
  axiom (TwIRecBt (IRec c l h) _ btfun _) = do
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

instance Element ls i => Element (ls :!: TwIRecBt mB mF c u x r) i where
  data Elm (ls :!: (TwIRecBt mB mF c u x r)) i = ElmBtIRec !x [r] !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: (TwIRecBt mB mF c u x r))   = Arg ls :. (x, [r])
  getArg (ElmBtIRec x s _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtIRec _ _ i _ ) = i
  {-# Inline getArg #-}
  {-# Inline getIdx #-}

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (Elm ls (is:.i)) (us:.u) (cs:.c) (is:.i)
  , MkStream m ls (is:.i)
  ) => MkStream m (ls :!: TwIRec m (cs:.c) (us:.u) x) (is:.i) where
  mkStream (ls :!: TwIRec (IRec c l h) fun) vs us is
    = mapM (\(s,tt,ii) -> (\res -> ElmIRec res ii s) <$> fun h tt)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (is:.i)
  , TableStaticVar (us:.u) (cs:.c) (is:.i)
  , AddIndexDense (Elm ls (is:.i)) (us:.u) (cs:.c) (is:.i)
  , MkStream mB ls (is:.i)
  ) => MkStream mB (ls :!: TwIRecBt mB mF (cs:.c) (us:.u) x r) (is:.i) where
  mkStream (ls :!: TwIRecBt (IRec c l h) fwd bt mrph) vs us is
    = mapM (\(s,tt,ii) -> (\res bb -> ElmBtIRec res bb ii s) <$> (mrph $ fwd h tt) <*> bt h tt)
    . addIndexDense c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy (us:.u)) c vs is) us (tableStreamIndex (Proxy :: Proxy (us:.u)) c vs is)
  {-# Inline mkStream #-}

