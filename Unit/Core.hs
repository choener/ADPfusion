
-- |
--
-- TODO the 'mkStream' instances here are probably wonky for everything that is
-- non-static.
--
-- TODO should @d@ in each case here be @d==0@? What is the exact meaning @d@
-- should convey?

module ADPfusion.Unit.Core where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (singleton,map,filter,Step(..))
import Debug.Trace
import Prelude hiding (map,filter)

import Data.PrimitiveArray hiding (map)

import ADPfusion.Core.Classes
import ADPfusion.Core.Multi



type instance InitialContext (Unit I) = IStatic 0

type instance InitialContext (Unit O) = OStatic 0

type instance InitialContext (Unit C) = Complement

data instance RunningIndex (Unit t) = RiUnit



instance
  ( Monad m
  )
  ⇒ MkStream m (IStatic d) S (Unit I) where
  mkStream Proxy S grd LtUnit Unit
    = staticCheck# grd
    . singleton $ ElmS RiUnit
  {-# Inline mkStream #-}

instance
  ( Monad m
  )
  ⇒ MkStream m (IVariable d) S (Unit I) where
  mkStream Proxy S grd LtUnit Unit
    = staticCheck# grd
    . singleton $ ElmS RiUnit
  {-# Inline mkStream #-}

instance
  ( Monad m
  )
  ⇒ MkStream m (OStatic d) S (Unit O) where
  mkStream Proxy S grd LtUnit Unit
    = staticCheck# grd
    . singleton $ ElmS RiUnit
  {-# Inline mkStream #-}

instance
  ( Monad m
  )
  ⇒ MkStream m Complement S (Unit C) where
  mkStream Proxy S grd LtUnit Unit
    = staticCheck# grd
    . singleton $ ElmS RiUnit
  {-# Inline mkStream #-}

--instance
--  forall m ps p is
--  . ( Monad m
--    , MkStream m ps S is
--    )
--  ⇒ MkStream m ('(:.) ps p) S (is:.Unit I) where
--  mkStream Proxy S grd (us:.._) (is:._)
--    = map (\(ElmS zi) -> ElmS $ zi :.: RiU)
--    $ mkStream (Proxy ∷ Proxy ps) S grd us is
--  {-# Inline mkStream #-}
--
--instance
--  forall m ps p is
--  . ( Monad m
--    , MkStream m ps S is
--    )
--  ⇒ MkStream m ('(:.) ps p) S (is:.Unit O) where
--  mkStream Proxy S grd (us:.._) (is:._)
--    = map (\(ElmS zi) -> ElmS $ zi :.: RiU)
--    $ mkStream (Proxy ∷ Proxy ps) S grd us is
--  {-# Inline mkStream #-}
--
--instance
--  forall m ps p is
--  . ( Monad m
--    , MkStream m ps S is
--    )
--  ⇒ MkStream m ('(:.) ps p) S (is:.Unit C) where
--  mkStream Proxy S grd (us:.._) (is:._)
--    = map (\(ElmS zi) -> ElmS $ zi :.: RiU)
--    $ mkStream (Proxy ∷ Proxy ps) S grd us is
--  {-# Inline mkStream #-}
--
--
--
--instance TableStaticVar pos c u (Unit I) where
--  tableStreamIndex _ _ _ _ = Unit
--  {-# Inline [0] tableStreamIndex #-}
--
--instance TableStaticVar pos c u (Unit O) where
--  tableStreamIndex _ _ _ _ = Unit
--  {-# Inline [0] tableStreamIndex #-}
--
--instance TableStaticVar pos c u (Unit C) where
--  tableStreamIndex _ _ _ _ = Unit
--  {-# Inline [0] tableStreamIndex #-}

