
-- | Instances to allow 'Subword's to be used as index structures in
-- @ADPfusion@.

module ADP.Fusion.Base.Subword where

import Data.Vector.Fusion.Stream.Monadic (singleton,filter,enumFromStepN,map,unfoldr)
import Debug.Trace
import Prelude hiding (map,filter)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



instance RuleContext (Subword I) where
  type Context (Subword I) = InsideContext ()
  initialContext _ = IStatic ()
  {-# Inline initialContext #-}

instance RuleContext (Subword O) where
  type Context (Subword O) = OutsideContext (Int:.Int)
  initialContext _ = OStatic (0:.0)
  {-# Inline  initialContext #-}

instance RuleContext (Subword C) where
  type Context (Subword C) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}

-- TODO write instance

-- instance RuleContext (Complement Subword)



instance (Monad m) => MkStream m S (Subword I) where
  mkStream S (IStatic ()) (Subword (_:.h)) (Subword (i:.j))
    = staticCheck (i>=0 && i==j && j<=h)
    . singleton
    $ ElmS (subword i i) (subword 0 0)
  -- NOTE it seems that a static check within an @IVariable@ context
  -- destroys fusion; maybe because of the outer flatten? We don't actually
  -- need a static check anyway because the next flatten takes care of
  -- conditional checks. @filter@ on the other hand, does work.
  -- TODO test with and without filter using quickcheck
  mkStream S (IVariable ()) (Subword (_:.h)) (Subword (i:.j))
    = filter (const $ 0<=i && i<=j && j<=h) . singleton $ ElmS (subword i i) (subword 0 0)
  {-# Inline mkStream #-}

instance (Monad m) => MkStream m S (Subword O) where
  mkStream S (OStatic (di:.dj)) (Subword (_:.h)) (Subword (i:.j))
    = staticCheck (i==0 && j+dj==h) . singleton $ ElmS (subword i j) (Subword (i:.j+dj))
  mkStream S (OFirstLeft (di:.dj)) (Subword (_:.h)) (Subword (i:.j))
    = let i' = i-di
      in  staticCheck (0 <= i' && i<=j && j+dj<=h) . singleton $ ElmS (subword i' i') (subword i' i')
  mkStream S (OLeftOf (di:.dj)) (Subword (_:.h)) (Subword (i:.j))
    = let i' = i-di
      in  staticCheck (0 <= i' && i<=j && j+dj<=h)
    $ map (\k -> ElmS (subword 0 k) (subword k j))
    $ enumFromStepN 0 1 (i'+1)
  mkStream S e _ _ = error $ show e ++ "maybe only inside syntactic terminals on the RHS of an outside rule?" -- TODO mostly because I'm not sure if that would be useful
  {-# Inline mkStream #-}

instance (Monad m) => MkStream m S (Subword C) where
  mkStream S Complemented (Subword (_:.h)) (Subword (i:.j))
    = map (\(k,l) -> ElmS (subword k l) (subword k l))
    $ unfoldr go (i,i)
    where go (k,l)
            | k >h || k >j = Nothing
            | l==h || l==j = Just ( (k,l) , (k+1,k+1) )
            | otherwise    = Just ( (k,l) , (k  ,l+1) )
          {-# Inline [0] go #-}
  {-# Inline mkStream #-}



instance
  ( Monad m
  , MkStream m S is
--  , Context (is:.Subword) ~ (Context is:.(InsideContext ()))
  ) => MkStream m S (is:.Subword I) where
  mkStream S (vs:.IStatic ()) (lus:.Subword (_:.h)) (ixs:.Subword(i:.j))
    = staticCheck (i>=0 && i==j && j<=h)
    . map (\(ElmS zi zo) -> ElmS (zi:.subword i i) (zo:.subword 0 0))
    $ mkStream S vs lus ixs
  mkStream S (vs:.IVariable ()) (lus:.Subword (_:.h)) (ixs:.Subword (i:.j))
    = map (\(ElmS zi zo) -> ElmS (zi:.subword i i) (zo:.subword 0 0))
    . filter (const $ 0<=i && i<=j && j<=h)
    $ mkStream S vs lus ixs
  {-# Inline mkStream #-}

instance (TblConstraint u ~ TableConstraint) => TableStaticVar u (Subword I) where
  tableStaticVar _ _ (IStatic   d) _ = IVariable d
  tableStaticVar _ _ (IVariable d) _ = IVariable d
  tableStreamIndex _ c _ (Subword (i:.j))
    | c==EmptyOk  = subword i j
    | c==NonEmpty = subword i (j-1)
    | c==NonEmpty = error "A.F.B.Subword ???"
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

-- | This instance is chosen if we consider an outside table (i.e.
-- a syntactic variable) in an outside index.
--
-- TODO @tableStreamIndex@ needs to be fixed

instance TableStaticVar (u O) (Subword O) where
  tableStaticVar _ _ (OStatic  d) _ = OFirstLeft d
  tableStaticVar _ _ (ORightOf d) _ = OFirstLeft d
  tableStreamIndex _ c _ (Subword (i:.j)) = subword i j
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

-- | This instance is chosen if we consider an inside table (i.e.
-- a terminal symbol!) in an outside index.
--
-- TODO @tableStreamIndex@ needs to be fixed

instance TableStaticVar (u I) (Subword O) where
  tableStaticVar _ _ (OStatic    d) _ = ORightOf d
  tableStaticVar _ _ (ORightOf   d) _ = ORightOf d
  tableStaticVar _ _ (OFirstLeft d) _ = OLeftOf d
  tableStaticVar _ _ (OLeftOf    d) _ = OLeftOf d
  tableStreamIndex _ c _ (Subword (i:.j)) = subword i j
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

