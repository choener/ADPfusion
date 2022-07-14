
module ADPfusion.PointL.SynVar where

import qualified Data.Vector.Fusion.Stream.Monadic as SP
import Data.Strict.Tuple

import Data.PrimitiveArray as PA hiding (map)

import ADPfusion.Core
import ADPfusion.PointL.Core

-- * Taking care of split non-terminals.

type instance LeftPosTy (IStatic   d) (Split uId Final    (TwITbl b s m (Dense v) (cs:.c) (us:.u) x)) (PointL I) = IVariable d
type instance LeftPosTy (IVariable d) (Split uId Fragment (TwITbl b s m (Dense v) (cs:.c) (us:.u) x)) (PointL I) = IVariable d

instance
  ( split ~ Split uId Fragment (TwITbl b s m (Dense v) (cs:.c) (us:.u) x)
  , left ~ LeftPosTy (IVariable 0) split (PointL I)
  , Monad m, MkStream m left ls (PointL I), TermStaticVar (IVariable 0) split (PointL I)
  ) => MkStream m (IVariable 0) (ls :!: Split uId Fragment (TwITbl b s m (Dense v) (cs:.c) (us:.u) x)) (PointL I) where
--{{{
  {-# Inline mkStream #-}
  mkStream proxy (ls :!: split@(Split _)) grd us i
    = SP.map (\elm ->
        let ri = RiPlI $ fromPointL i
        in  ElmSplitITbl (Proxy @uId) () ri elm i)
    $ mkStream (Proxy :: Proxy left) ls
        (termStaticCheck proxy split us i grd)
        us i
--}}}

-- |
--
-- TODO it might be possible to generalize this code?

instance
  ( us ~ SplitIxTy uId (SameSid uId (Elm ls (PointL I))) (Elm ls (PointL I))
  , split ~ Split uId Final (TwITbl b s m (Dense v) (cs:.c) (us:.PointL I) x)
  , left ~ LeftPosTy (IStatic 0) split (PointL I)
  , Monad m, MkStream m left ls (PointL I), TermStaticVar (IStatic 0) split (PointL I)
  , SplitIxCol uId (SameSid uId (Elm ls (PointL I))) (Elm ls (PointL I))
  , PrimArrayOps (Dense v) (us:.PointL I) x
  ) => MkStream m (IStatic 0) (ls :!: Split uId Final (TwITbl b s m (Dense v) (cs:.c) (us:.PointL I) x)) (PointL I) where
--{{{
  {-# Inline mkStream #-}
  mkStream proxy (ls :!: split@(Split (TW (ITbl _ arr) _))) grd us i
    = SP.map (\elm ->
      let jx = collectIx (Proxy @uId) elm :. i
          val = arr PA.! jx
          ri = RiPlI $ fromPointL i
      in  ElmSplitITbl (Proxy @uId) val ri elm i)
    $ mkStream (Proxy :: Proxy left) ls
        (termStaticCheck proxy split us i grd)
        us i
--}}}

-- * 'TermStream' : capture syntactic variables in a terminal position.

instance (Monad m, PrimArrayOps arr (PointL I) x, TermStream m ps ts s is)
  => TermStream m (ps:.IStatic 0) (TermSymbol ts (TwITbl bo so m arr c (PointL I) x)) s (is:.PointL I) where
--{{{
  {-# Inline termStream #-}
  termStream Proxy (ts:| TW (ITbl _ arr) f) (us:..u) (is:.i)
    = SP.map (\(TState s ii ee) ->
        let (PointL ri) = i
        in  TState s (ii:.:RiPlI ri) (ee:.arr!i))
    . termStream (Proxy :: Proxy ps) ts us is
--}}}

instance TermStaticVar (IStatic d) (TwITbl bo so m arr c (PointL I) x) (PointL I) where
--{{{
  -- | Calculate how much the index changes.
  --
  -- TODO replace '0' by an appropriate (EmptyOk vs not) amount
  {-# Inline [0] termStreamIndex #-}
  termStreamIndex Proxy _ (PointL j) = PointL $ j - 0
  {-# Inline [0] termStaticCheck #-}
  termStaticCheck Proxy _ _ _ grd = grd
--}}}

instance TermStaticVar (IStatic d) (Split uId fragTy (TwITbl bo so m arr c i x)) (PointL I) where
--{{{
  -- | Calculate how much the index changes.
  --
  -- TODO replace '0' by an appropriate (EmptyOk vs not) amount
  {-# Inline [0] termStreamIndex #-}
  termStreamIndex Proxy _ (PointL j) = PointL $ j - 0
  {-# Inline [0] termStaticCheck #-}
  termStaticCheck Proxy _ _ _ grd = grd
--}}}

instance TermStaticVar (IVariable d) (Split uId fragTy (TwITbl bo so m arr c i x)) (PointL I) where
--{{{
  -- | Calculate how much the index changes.
  --
  -- TODO replace '0' by an appropriate (EmptyOk vs not) amount
  {-# Inline [0] termStreamIndex #-}
  termStreamIndex Proxy _ (PointL j) = PointL $ j - 0
  {-# Inline [0] termStaticCheck #-}
  termStaticCheck Proxy _ _ _ grd = grd
--}}}

