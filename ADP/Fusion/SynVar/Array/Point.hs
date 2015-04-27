
module ADP.Fusion.SynVar.Array.Point where

import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.SynVar.Array.Type
import           ADP.Fusion.SynVar.Backtrack



instance
  ( Monad m
  , Element ls PointL
  , PrimArrayOps arr PointL x
  , MkStream m ls PointL
  ) => MkStream m (ls :!: ITbl m arr PointL x) PointL where
  mkStream (ls :!: ITbl _ _ c t _) (IStatic ()) u j@(PointL pj)
    = let ms = minSize c in ms `seq`
    S.map (ElmITbl (t!j) j (PointL 0))
    $ mkStream ls (IVariable ()) u (PointL $ pj - ms)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls PointL
  , PrimArrayOps arr PointL x
  , MkStream mB ls PointL
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr PointL x) mF mB r) PointL where
  mkStream (ls :!: BtITbl c t bt) (IStatic ()) u j@(PointL pj)
    = let ms = minSize c in ms `seq`
    S.mapM (\s -> bt u j >>= \bb -> return $ ElmBtITbl (t!j) (bb {-bt u j-}) j (PointL 0) s)
    $ mkStream ls (IVariable ()) u (PointL $ pj - ms)
  {-# INLINE mkStream #-}

instance
  ( Monad m
  , Element ls (Outside PointL)
  , PrimArrayOps arr (Outside PointL) x
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: ITbl m arr (Outside PointL) x) (Outside PointL) where
  mkStream (ls :!: ITbl _ _ c t _) (OStatic d) u (O (PointL pj))
    = let ms = minSize c in ms `seq`
    S.map (\z -> let o = getOmx z
                 in  ElmITbl (t ! o) o o z)
    $ mkStream ls (OFirstLeft d) u (O $ PointL $ pj - ms)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (Outside PointL)
  , PrimArrayOps arr (Outside PointL) x
  , MkStream mB ls (Outside PointL)
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr (Outside PointL) x) mF mB r) (Outside PointL) where
  mkStream (ls :!: BtITbl c t bt) (OStatic d) u (O (PointL pj))
    = let ms = minSize c in ms `seq`
    S.mapM (\s -> let o = getOmx s in bt u o >>= \bb -> return $ ElmBtITbl (t!o) (bb{-bt u o-}) o o s)
    $ mkStream ls (OFirstLeft d) u (O $ PointL $ pj - ms)
  {-# INLINE mkStream #-}

