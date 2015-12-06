
-- | Instance code for @Inside@, @Outside@, and @Complement@ indices.
--
-- TODO actual @Outside@ and @Complement@ code ...
--
-- TODO we have quite a lot of @subword i j@ code where only the @type@
-- is different; check if @coerce@ yields improved performance or if the
-- compiler optimizes this out!

module ADP.Fusion.SynVar.Indices.Subword where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..),filter)
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM,filter)
import Debug.Trace

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



-- |
-- @
-- Table: Inside
-- Grammar: Inside
--
-- The minSize condition for @IStatic@ is guaranteed via the use of
-- @tableStreamIndex@ (not here, in individual synvars), where @j@ is set
-- to @j-1@ for the next-left symbol!
-- @

instance
  ( IndexHdr a us (Subword I) is (Subword I)
  ) => AddIndexDense a (us:.Subword I) (is:.Subword I) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:.Subword (_:.u)) (is:.Subword (i:.j))
    = staticCheck (j<=u)
    . map (\(SvS s a t y') -> let RiSwI l = getIndex a (Proxy :: PRI is (Subword I))
                                  lj = subword l j
                              in  SvS s a (t:.lj) (y' :.: RiSwI j) )
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.IVariable ()) (us:.Subword (_:.u)) (is:.Subword (i:.j))
    = staticCheck (j<=u)
    . flatten mk step . addIndexDenseGo cs vs us is
    where mk   svS = let RiSwI l = getIndex (sIx svS) (Proxy :: PRI is (Subword I))
                     in  return $ svS :. (j - l - csize)
          step (svS@(SvS s a t y') :. zz)
            | zz >= 0 = do let RiSwI k = getIndex a (Proxy :: PRI is (Subword I))
                               l = j - zz ; kl = subword k l
                           return $ Yield (SvS s a (t:.kl) (y' :.: RiSwI l)) (svS :. zz-1)
            | otherwise =  return $ Done
          csize = delay_inline minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

-- |
-- @
-- Table: Outside
-- Grammar: Outside
-- @
--
-- TODO Take care of @c@ in all cases to correctly handle @NonEmpty@ tables
-- and the like.

instance
  ( IndexHdr a us (Subword O) is (Subword O)
  ) => AddIndexDense a (us:.Subword O) (is:.Subword O) where
  addIndexDenseGo (cs:.c) (vs:.OStatic (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = map (\(SvS s a t y') -> let RiSwO _ _ k _ = getIndex a (Proxy :: PRI is (Subword O))
                                  kj = subword k (j+dj)
                              in  SvS s a (t:.kj) (y' :.: RiSwO i j k (j+dj)) )
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.ORightOf (di:.dj)) (us:.Subword (_:.h)) (is:.Subword (i:.j))
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = return (svS :. j+dj)
          step (svS@(SvS s a t y') :. l)
            | l <= h = let RiSwO k _ _ _ = getIndex a (Proxy :: PRI is (Subword O))
                           kl = subword k l
                           jdj = j+dj
                       in  return $ Yield (SvS s a (t:.kl) (y' :.: RiSwO jdj jdj k l)) (svS :. l+1)
            | otherwise = return Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  addIndexDenseGo _ (_:.OFirstLeft _) _ _ = error "SynVar.Indices.Subword : OFirstLeft"
  addIndexDenseGo _ (_:.OLeftOf    _) _ _ = error "SynVar.Indices.Subword : LeftOf"
  {-# Inline addIndexDenseGo #-}

-- |
-- @
-- Table: Inside
-- Grammar: Outside
-- @
--
-- TODO take care of @c@

instance
  ( IndexHdr a us (Subword I) is (Subword O)
  ) => AddIndexDense a (us:.Subword I) (is:.Subword O) where
  addIndexDenseGo (cs:.c) (vs:.OStatic (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = map (\(SvS s a t y') -> let RiSwO _ k li l = getIndex a (Proxy :: PRI is (Subword O))
                                  klI = subword (k-dj) (l-dj)
                              in  SvS s a (t:.klI) (y':.:RiSwO (k-dj) (l-dj) li l))
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.ORightOf d) (us:.u) (is:.Subword (i:.j))
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = let RiSwO _ l _ _ = getIndex (sIx svS) (Proxy :: PRI is (Subword O))
                   in  return (svS :. l :. l + csize)
          step (svS@(SvS s a t y') :. k :. l)
            | l <= oj   = return $ Yield (SvS s a (t:.klI) (y' :.: RiSwO k l oi oj))
                                         (svS :. k :. l+1)
            | otherwise = return $ Done
            where RiSwO _ _ oi oj = getIndex a (Proxy :: PRI is (Subword O))
                  klI = subword k l
          csize = minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  addIndexDenseGo (cs:.c) (vs:.OFirstLeft (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = map (\(SvS s a t y') -> let RiSwO _ k l lj = getIndex a (Proxy :: PRI is (Subword O))
                                  klI = subword k $ i - di
                              in  SvS s a (t:.klI) (y' :.: RiSwO k (i-di) l lj))
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.OLeftOf d) (us:.u) (is:.Subword (i:.j))
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = let RiSwO _ l _ _ = getIndex (sIx svS) (Proxy :: PRI is (Subword O))
                   in  return $ svS :. l
          step (svS@(SvS s a t y') :. l)
            | l <= i    = let RiSwO _ k oi oj = getIndex a (Proxy :: PRI is (Subword O))
                              klI = subword k l
                          in  return $ Yield (SvS s a (t:.klI) (y' :.: RiSwO k l oi oj))
                                             (svS :. l+1)
            | otherwise = return $ Done
          csize = minSize c
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}




-- TODO
-- @
-- Table: Inside
-- Grammar: Complement
-- @

instance
  ( IndexHdr a us (Subword I) is (Subword C)
  ) => AddIndexDense a (us:.Subword I) (is:.Subword C) where
  addIndexDenseGo (cs:.c) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(SvS s a t y') -> let kk@(RiSwC ki kj) = getIndex a (Proxy :: PRI is (Subword C))
                              in  SvS s a (t:.subword ki kj) (y':.:kk))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

-- TODO
-- @
-- Table: Outside
-- Grammar: Complement
-- @

instance
  ( IndexHdr a us (Subword O) is (Subword C)
  ) => AddIndexDense a (us:.Subword O) (is:.Subword C) where
  addIndexDenseGo (cs:.c) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(SvS s a t y') -> let kk@(RiSwC ki kj) = getIndex a (Proxy :: PRI is (Subword C))
                              in  SvS s a (t:.subword ki kj) (y':.:kk))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

-- |
-- @
-- Table: Complement
-- Grammar: Complement
-- @

instance
  ( IndexHdr a us (Subword C) is (Subword C)
  ) => AddIndexDense a (us:.Subword C) (is:.Subword C) where
  addIndexDenseGo (cs:.c) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(SvS s a t y') -> let k = getIndex a (Proxy :: PRI is (Subword C))
                                  RiSwC ki kj = k
                              in  SvS s a (t:.subword ki kj) (y':.:k))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}


