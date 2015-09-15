
module ADP.Fusion.SynVar.Array.Point where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import Prelude hiding (map,mapM)
--import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Base
import           ADP.Fusion.SynVar.Array.Type
import           ADP.Fusion.SynVar.Backtrack
import           ADP.Fusion.SynVar.Indices



instance
  ( Monad m
  , Element ls PointL
  , PrimArrayOps arr PointL x
  , MkStream m ls PointL
  ) => MkStream m (ls :!: ITbl m arr PointL x) PointL where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar c vs is) us (tableStreamIndex c vs is)
{-
    = let ms = minSize c in ms `seq`
    map (ElmITbl (t!j) j (PointL 0))
    $ mkStream ls (IVariable d) u (PointL $ pj - ms)
  -- We can't really make sure that this is the only time we access the
  -- ITbl, so the user should know what they are doing.
  mkStream (ls :!: ITbl _ _ c t _) (IVariable d) u j@(PointL pj)
    = flatten mk step Unknown $ mkStream ls (IVariable d) u (delay_inline PointL $! pj - ms)
    where mk s = let PointL k = getIdx s in return (s :. k)
          step (s :. k)
            | k+ms>pj   = return $ Done
            | otherwise = return $ Yield (ElmITbl (t!PointL k) (PointL k) (PointL 0) s) (s :. k+1)
          !ms = minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
-}
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls PointL
  , PrimArrayOps arr PointL x
  , MkStream mB ls PointL
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr PointL x) mF mB r) PointL where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = mapM (\(s,ii,oo,ii',oo') -> bt us ii >>= \ ~bb -> return $ ElmBtITbl (t!ii) bb ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar c vs is) us (tableStreamIndex c vs is)
{-
    = let ms = minSize c in ms `seq`
    mapM (\s -> bt u j >>= \bb -> return $ ElmBtITbl (t!j) (bb {-bt u j-}) j (PointL 0) s)
    $ mkStream ls (IVariable d) u (PointL $ pj - ms)
-}
  {-# INLINE mkStream #-}

{-
instance
  ( Monad m
  , Element ls (Outside PointL)
  , PrimArrayOps arr (Outside PointL) x
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: ITbl m arr (Outside PointL) x) (Outside PointL) where
  mkStream (ls :!: ITbl _ _ c t _) (OStatic d) u (O (PointL pj))
    = let ms = minSize c in ms `seq`
    map (\z -> let o = getOmx z
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
    mapM (\s -> let o = getOmx s in bt u o >>= \bb -> return $ ElmBtITbl (t!o) (bb{-bt u o-}) o o s)
    $ mkStream ls (OFirstLeft d) u (O $ PointL $ pj - ms)
  {-# INLINE mkStream #-}
-}

