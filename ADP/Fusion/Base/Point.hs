
{-# Language TypeFamilies #-}
{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}

module ADP.Fusion.Base.Point where

import Data.Vector.Fusion.Stream.Monadic (singleton)

import Data.PrimitiveArray

import ADP.Fusion.Base.Classes



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
  mkStream S IStatic   _ (PointL j)
    = staticCheck (0==j) . singleton $ ElmS (PointL 0) (PointL 0)
  mkStream S IVariable _ (PointL j)
    = staticCheck (0<=j) . singleton $ ElmS (PointL j) (PointL 0)
  {-# Inline mkStream #-}

instance (Monad m) => MkStream m S (Outside PointL) where
  mkStream S (OStatic d) (O (PointL u)) (O (PointL i))
    = staticCheck (i>=0 && i+d<=u) . singleton $ ElmS (O $ PointL i) (O . PointL $ i+d)
  mkStream S (OVariable FarLeft d) (O (PointL u)) (O (PointL i))
    = staticCheck (i>=0 && i+d<=u) . singleton $ ElmS (O $ PointL i) (O . PointL $ i+d)
  {-# Inline mkStream #-}

{-
instance (Monad m) => MkStream m S PointL where
  mkStream S (Variable Check Nothing) (PointL (l:.u)) (PointL (i:.j))
    = staticCheck (j>=l && j<=u && i<=j) $ S.singleton (ElmS $ PointL (i:.i))
  mkStream S Static (PointL (l:.u)) (PointL (i:.j))
    = staticCheck (i==j) $ S.singleton (ElmS $ PointL (i:.i))
--  mkStream S z (PointL (l:.u)) (PointL (i:.j)) = error $ "S.PointL write me: " ++ show z
  {-# INLINE mkStream #-}
-}
