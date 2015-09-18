
module ADP.Fusion.SynVar.Array.Point where

import Data.Strict.Tuple hiding (snd)
import Data.Vector.Fusion.Stream.Monadic
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import Prelude hiding (map,mapM)
import Data.Proxy
--import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Base
import           ADP.Fusion.SynVar.Array.Type
import           ADP.Fusion.SynVar.Backtrack
import           ADP.Fusion.SynVar.Indices



{-
instance
  ( Monad m
  , Element ls (PointL I)
  , PrimArrayOps arr u x
  , TblConstraint u ~ TableConstraint
  , AddIndexDense (Z:.PointL I) (Z:.u) (Z:.PointL I)
  , MkStream m ls (PointL I)
  ) => MkStream m (ls :!: ITbl m arr u x) (PointL I) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (PointL I)
  , PrimArrayOps arr u x
  , MkStream mB ls (PointL I)
  , TblConstraint u ~ TableConstraint
  , AddIndexDense (Z:.PointL I) (Z:.u) (Z:.PointL I)
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr u x) mF mB r) (PointL I) where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = mapM (\(s,ii,oo,ii',oo') -> bt us' ii >>= \ ~bb -> return $ ElmBtITbl (t!ii) bb ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
    where !us' = snd $ bounds t
  {-# INLINE mkStream #-}
-}



{-
instance
  ( Monad m
  , Element ls (PointL O)
  , PrimArrayOps arr (Outside u) x
  , TblConstraint (Outside u) ~ TableConstraint
  , AddIndexDense (Outside (Z:.PointL)) (Outside (Z:.u)) (Outside (Z:.PointL))
  , MkStream m ls (Outside PointL)
  ) => MkStream m (ls :!: ITbl m arr (Outside u) x) (Outside PointL) where
  mkStream (ls :!: ITbl _ _ c t _) vs us is
  -- TODO need to decide: shall we keep @(Outside (is:.i))@ as the encoding
  -- or should we swtich to @is :. Outside i@ with the assumption that the
  -- necessary things in @is@ will also be @Outside@ ?
  -- (same for @Complement@)
    = map (\(s,ii,oo,ii',oo') -> ElmITbl (t!ii) ii' oo' s)
    . addIndexDense1 c vs us is
    $ mkStream ls (tableStaticVar (Proxy :: Proxy u) c vs is) us (tableStreamIndex (Proxy :: Proxy u) c vs is)
  {-
  mkStream (ls :!: ITbl _ _ c t _) (OStatic d) u (O (PointL pj))
    = let ms = minSize c in ms `seq`
    map (\z -> let o = getOmx z
                 in  ElmITbl (t ! o) o o z)
    $ mkStream ls (OFirstLeft d) u (O $ PointL $ pj - ms)
  -}
  {-# Inline mkStream #-}
-}

{-
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

