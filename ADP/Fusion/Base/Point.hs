
module ADP.Fusion.Base.Point where

import Data.Vector.Fusion.Stream.Monadic (singleton,map,filter,Step(..))
import Debug.Trace
import Prelude hiding (map,filter)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



instance RuleContext (PointL I) where
  type Context (PointL I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

instance RuleContext (PointL O) where
  type Context (PointL O) = OutsideContext Int
  initialContext _ = OStatic 0
  {-# Inline initialContext #-}

instance RuleContext (PointL C) where
  type Context (PointL C) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}



instance (Monad m) => MkStream m S (PointL I) where
  mkStream S (IStatic d) (PointL u) (PointL j)
    = staticCheck (j>=0 && j<=d) . singleton $ ElmS (PointL 0) (PointL 0)
  mkStream S (IVariable _) (PointL u) (PointL j)
    = staticCheck (0<=j) . singleton $ ElmS (PointL 0) (PointL 0)
  {-# Inline mkStream #-}

instance (Monad m) => MkStream m S (PointL O) where
  mkStream S (OStatic d) (PointL u) (PointL i)
    = staticCheck (i>=0 && i+d<=u && u == i) . singleton $ ElmS (PointL i) (PointL $ i+d)
  mkStream S (OFirstLeft d) (PointL u) (PointL i)
    = staticCheck (i>=0 && i+d<=u) . singleton $ ElmS (PointL i) (PointL $ i+d)
  {-# Inline mkStream #-}



instance
  ( Monad m
  , MkStream m S is
--  , Context (is:.PointL) ~ (Context is:.(InsideContext Int))
  ) => MkStream m S (is:.PointL I) where
  mkStream S (vs:.IStatic d) (lus:.PointL u) (is:.PointL i)
    = staticCheck (i>=0 && i<=d && i<=u)
    . map (\(ElmS zi zo) -> ElmS (zi:.PointL 0) (zo:.PointL 0))
    $ mkStream S vs lus is
  {-
  mkStream S (vs:.IVariable ) (lus:.PointL u) (is:.PointL i)
    = flatten mk step Unknown $ mkStream S vs lus is
    where mk e = i `seq` return (e,i)
          step (ElmS zi zo,k )
            | k>=0 && k<=u = return $ Yield (ElmS (zi:.PointL k) (zo:.PointL 0)) (ElmS zi zo, -1)
            | otherwise    = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  -}
  -- TODO here, we have a problem in the interplay of @staticCheck@ or
  -- @flatten@ and how we modify @is@. Apparently, once we demand to know
  -- about @i@, fusion breaks down.
  mkStream S (vs:.IVariable d) (lus:.PointL u) (is:.PointL i)
    = staticCheck (i>=0 && i<=u)
    $ map (\(ElmS zi zo) -> ElmS (zi:.PointL 0) (zo:.PointL 0))
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}

instance
  ( Monad m
  , MkStream m S is
--  , Context (Outside (is:.PointL)) ~ (Context (Outside is) :. OutsideContext Int)
  ) => MkStream m S (is:.PointL O) where
  mkStream S (vs:.OStatic d) (lus:.PointL u) (is:.PointL i)
    = staticCheck (i>=0 && i+d == u)
    . map (\(ElmS zi zo) -> ElmS (zi:.PointL i) (zo:.(PointL $ i+d)))
    $ mkStream S vs lus is
  mkStream S (vs:.OFirstLeft d) (us:.PointL u) (is:.PointL i)
    = staticCheck (i>=0 && i+d<=u)
    . map (\(ElmS zi zo) -> ElmS (zi:.PointL i) (zo:.(PointL $ i+d)))
    $ mkStream S vs us is
  {-# Inline mkStream #-}

instance (TblConstraint u ~ TableConstraint) => TableStaticVar u (PointL I) where
  tableStaticVar _ _ (IStatic   d) _ = IVariable d
  tableStaticVar _ _ (IVariable d) _ = IVariable d
  -- NOTE this code used to destroy fusion. If we inline tableStreamIndex
  -- very late (after 'mkStream', probably) then everything works out.
  tableStreamIndex _ c _ (PointL j)
    | c==EmptyOk  = PointL j
    | c==NonEmpty = PointL $ j-1
    | c==OnlyZero = PointL j -- this should then actually request a size in 'tableStaticVar' ...
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance (TblConstraint u ~ TableConstraint) => TableStaticVar u (PointL O) where
  tableStaticVar   _ _ (OStatic d) _ = OFirstLeft d
  tableStreamIndex _ c _ (PointL j)
    | c==EmptyOk  = (PointL j)
    | c==NonEmpty = (PointL $ j-1)
    | c==OnlyZero = (PointL j) -- this should then actually request a size in 'tableStaticVar' ...
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

