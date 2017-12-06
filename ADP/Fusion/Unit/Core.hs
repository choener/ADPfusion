
-- |
--
-- TODO the 'mkStream' instances here are probably wonky for everything
-- that is non-static.

module ADP.Fusion.Unit.Core where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (singleton,map,filter,Step(..))
import Debug.Trace
import Prelude hiding (map,filter)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



instance RuleContext (Unit I) where
  type InitialContext (Unit I) = InsideContext ()
  initialContext Proxy = Proxy
  {-# Inline initialContext #-}

instance RuleContext (Unit O) where
  type InitialContext (Unit O) = OutsideContext ()
  initialContext Proxy = Proxy
  {-# Inline initialContext #-}

instance RuleContext (Unit C) where
  type InitialContext (Unit C) = ComplementContext
  initialContext Proxy = Proxy
  {-# Inline initialContext #-}

data instance RunningIndex (Unit t) = RiU



instance (Monad m) => MkStream m pos S (Unit I) where
  mkStream pos S grd LtUnit Unit = singleton $ ElmS RiU
  {-# Inline mkStream #-}

instance (Monad m) => MkStream m pos S (Unit O) where
  mkStream pos S grd LtUnit Unit = singleton $ ElmS RiU
  {-# Inline mkStream #-}

instance (Monad m) => MkStream m pos S (Unit C) where
  mkStream pos S grd LtUnit Unit = singleton $ ElmS RiU
  {-# Inline mkStream #-}

instance
  forall m ps p is
  . ( Monad m
    , MkStream m ps S is
    )
  ⇒ MkStream m ('(:.) ps p) S (is:.Unit I) where
  mkStream Proxy S grd (us:.._) (is:._)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiU)
    $ mkStream (Proxy ∷ Proxy ps) S grd us is
  {-# Inline mkStream #-}

instance
  forall m ps p is
  . ( Monad m
    , MkStream m ps S is
    )
  ⇒ MkStream m ('(:.) ps p) S (is:.Unit O) where
  mkStream Proxy S grd (us:.._) (is:._)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiU)
    $ mkStream (Proxy ∷ Proxy ps) S grd us is
  {-# Inline mkStream #-}

instance
  forall m ps p is
  . ( Monad m
    , MkStream m ps S is
    )
  ⇒ MkStream m ('(:.) ps p) S (is:.Unit C) where
  mkStream Proxy S grd (us:.._) (is:._)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiU)
    $ mkStream (Proxy ∷ Proxy ps) S grd us is
  {-# Inline mkStream #-}



instance TableStaticVar pos c u (Unit I) where
  tableStreamIndex _ _ _ _ = Unit
  {-# Inline [0] tableStreamIndex #-}

instance TableStaticVar pos c u (Unit O) where
  tableStreamIndex _ _ _ _ = Unit
  {-# Inline [0] tableStreamIndex #-}

instance TableStaticVar pos c u (Unit C) where
  tableStreamIndex _ _ _ _ = Unit
  {-# Inline [0] tableStreamIndex #-}

