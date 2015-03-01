
{-# Language TypeFamilies #-}
{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}

module ADP.Fusion.Base.Point where

import Data.Vector.Fusion.Stream.Monadic (singleton,map)
import Debug.Trace
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



instance RuleContext PointL where
  type Context PointL = InsideContext
  initialContext _ = IStatic

instance RuleContext (Outside PointL) where
  type Context (Outside PointL) = OutsideContext Int
  initialContext _ = OStatic 0

instance RuleContext (Complement PointL) where
  type Context (Complement PointL) = Complemented
  initialContext _ = Complemented

instance (Monad m) => MkStream m S PointL where
  mkStream S IStatic (PointL u) (PointL j)
    = staticCheck (0==j) . singleton $ ElmS (PointL 0) (PointL 0)
  mkStream S IVariable (PointL u) (PointL j)
    = staticCheck (0<=j) . singleton $ ElmS (PointL j) (PointL 0)
  {-# Inline mkStream #-}

instance (Monad m) => MkStream m S (Outside PointL) where
  mkStream S (OStatic d) (O (PointL u)) (O (PointL i))
    = staticCheck (i>=0 && i+d<=u && u == i) . singleton $ ElmS (O $ PointL i) (O . PointL $ i+d)
  mkStream S (OVariable FarLeft d) (O (PointL u)) (O (PointL i))
    = staticCheck (i>=0 && i+d<=u) . singleton $ ElmS (O $ PointL i) (O . PointL $ i+d)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  , Context (is:.PointL) ~ (Context is:.InsideContext)
  ) => MkStream m S (is:.PointL) where
  mkStream S (vs:.IStatic) (lus:.PointL u) (is:.PointL i)
    = staticCheck (i==0)
    . map (\(ElmS zi zo) -> ElmS (zi:.PointL i) (zo:.PointL 0))
    $ mkStream S vs lus is
  mkStream S (vs:.IVariable ) (lus:.PointL u) (is:.PointL i)
    = staticCheck (i>=0 && i<=u)
    $ map (\(ElmS zi zo) -> ElmS (zi:.PointL i) (zo:.PointL 0))
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}

instance
  ( Monad m
  , MkStream m S (Outside is)
  , Context (Outside (is:.PointL)) ~ (Context (Outside is) :. OutsideContext Int)
  ) => MkStream m S (Outside (is:.PointL)) where
  mkStream S (vs:.OStatic d) (O (lus:.PointL u)) (O (is:.PointL i))
    = staticCheck (i>=0 && i+d == u)
    . map (\(ElmS (O zi) (O zo)) -> ElmS (O (zi:.PointL i)) (O (zo:.(PointL $ i+d))))
    $ mkStream S vs (O lus) (O is)
  mkStream S (vs:.OVariable FarLeft d) (O (us:.PointL u)) (O (is:.PointL i))
    = staticCheck (i>=0 && i+d<=u)
    . map (\(ElmS (O zi) (O zo)) -> ElmS (O (zi:.PointL i)) (O (zo:.(PointL $ i+d))))
    $ mkStream S vs (O us) (O is)
  {-# Inline mkStream #-}

instance TableStaticVar PointL where
  tableStaticVar     _ _                = IVariable
  tableStreamIndex c _ (PointL j)
    | c==EmptyOk  = PointL j
    | c==NonEmpty = PointL $ j-1
    | c==OnlyZero = PointL j -- this should then actually request a size in 'tableStaticVar' ...
  {-# INLINE tableStaticVar   #-}
  {-# INLINE tableStreamIndex #-}

instance TableStaticVar (Outside PointL) where
  tableStaticVar     (OStatic d) _ = OVariable FarLeft d
  tableStreamIndex c _ (O (PointL j))
    | c==EmptyOk  = O (PointL j)
    | c==NonEmpty = O (PointL $ j-1)
    | c==OnlyZero = O (PointL j) -- this should then actually request a size in 'tableStaticVar' ...
  {-# INLINE tableStaticVar   #-}
  {-# INLINE tableStreamIndex #-}

