
-- |
--
-- TODO the 'mkStream' instances here are probably wonky for everything
-- that is non-static.

module ADP.Fusion.Base.Unit where

import Data.Vector.Fusion.Stream.Monadic (singleton,map,filter,Step(..))
import Debug.Trace
import Prelude hiding (map,filter)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



instance RuleContext (Unit I) where
  type Context (Unit I) = InsideContext ()
  initialContext _ = IStatic ()
  {-# Inline initialContext #-}

instance RuleContext (Unit O) where
  type Context (Unit O) = OutsideContext ()
  initialContext _ = OStatic ()
  {-# Inline initialContext #-}

instance RuleContext (Unit C) where
  type Context (Unit C) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}



instance (Monad m) => MkStream m S (Unit I) where
  mkStream S _ Unit Unit = singleton $ ElmS Unit Unit
  {-# Inline mkStream #-}

instance (Monad m) => MkStream m S (Unit O) where
  mkStream S _ Unit Unit = singleton $ ElmS Unit Unit
  {-# Inline mkStream #-}

instance (Monad m) => MkStream m S (Unit C) where
  mkStream S _ Unit Unit = singleton $ ElmS Unit Unit
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.Unit I) where
  mkStream S (vs:._) (us:._) (is:._)
    = map (\(ElmS zi zo) -> ElmS (zi:.Unit) (zo:.Unit))
    $ mkStream S vs us is
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.Unit O) where
  mkStream S (vs:._) (us:._) (is:._)
    = map (\(ElmS zi zo) -> ElmS (zi:.Unit) (zo:.Unit))
    $ mkStream S vs us is
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.Unit C) where
  mkStream S (vs:._) (us:._) (is:._)
    = map (\(ElmS zi zo) -> ElmS (zi:.Unit) (zo:.Unit))
    $ mkStream S vs us is
  {-# Inline mkStream #-}



instance (TblConstraint u ~ TableConstraint) => TableStaticVar u (Unit I) where
  tableStaticVar _ _ _ _ = IStatic ()
  tableStreamIndex _ _ _ _ = Unit
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}

instance (TblConstraint u ~ TableConstraint) => TableStaticVar u (Unit O) where
  tableStaticVar _ _ _ _ = OStatic ()
  tableStreamIndex _ _ _ _ = Unit
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}

instance (TblConstraint u ~ TableConstraint) => TableStaticVar u (Unit C) where
  tableStaticVar _ _ _ _ = Complemented
  tableStreamIndex _ _ _ _ = Unit
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}


