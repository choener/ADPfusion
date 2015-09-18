
-- | Instance code for @Inside@, @Outside@, and @Complement@ indices.
--
-- TODO actual @Outside@ and @Complement@ code ...

module ADP.Fusion.SynVar.Indices.Subword where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



-- |
-- @
-- Table: Inside
-- Grammar: Inside
-- @

instance
  ( AddIndexDense a us is
  , GetIndex a (is:.Subword I)
  , GetIx a (is:.Subword I) ~ (Subword I)
  ) => AddIndexDense a (us:.Subword I) (is:.Subword I) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:.Subword (_:.u)) (is:.Subword (i:.j))
    = staticCheck (j<=u)
    . map (\(S7 s a b y z y' z') -> let Subword (_:.l) = getIndex a (Proxy :: Proxy (is:.Subword I))
                                        lj = subword l j
                                        oo = subword 0 0
                                    in  S7 s a b (y:.lj) (z:.oo) (y':.lj) (z':.oo))
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.IVariable ()) (us:.Subword (_:.u)) (is:.Subword (i:.j))
    = staticCheck (j<=u)
    . flatten mk step . addIndexDenseGo cs vs us is
    where mk   (S7 s a b y z y' z') = let (Subword (_:.l)) = getIndex a (Proxy :: Proxy (is:.Subword I))
                                      in  return $ S8 s a b y z y' z' (j - l - csize)
          step (S8 s a b y z y' z' zz)
            | zz >= 0 = do let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword I))
                               l = j - zz ; kl = subword k l
                               oo = subword 0 0
                           return $ Yield (S7 s a b (y:.kl) (z:.oo) (y':.kl) (z':.oo)) (S8 s a b y z y' z' (zz-1))
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
  ( AddIndexDense a us is
  , GetIndex a (is:.Subword O)
  , GetIx a (is:.Subword O) ~ (Subword O)
  ) => AddIndexDense a (us:.Subword O) (is:.Subword O) where
  addIndexDenseGo (cs:.c) (vs:.OStatic (di:.dj)) (us:.u) (is:.Subword (i:.j))
    = map (\(S7 s a b y z y' z') -> let Subword (k:._) = getIndex b (Proxy :: Proxy (is:.Subword O))
                                        kj = subword k (j+dj)
                                        ij' = subword i (j+dj)
                                        oo = subword 0 0
                                    in  S7 s a b (y:.oo) (z:.kj) (y':.ij') (z':.kj))
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.ORightOf (di:.dj)) (us:.Subword (_:.h)) (is:.Subword (i:.j))
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk (S7 s a b y z y' z') = return (S7 s a b y z y' z' :. j+dj)
          step (S7 s a b y z y' z' :. l)
            | l <= h = let Subword (k:._) = getIndex a (Proxy :: Proxy (is:.Subword O))
                           kl = subword k l
                           jj = subword (j+dj) (j+dj)
                           oo = subword 0 0
                       in  return $ Yield (S7 s a b (y:.oo) (z:.kl) (y':.jj) (z':.kl)) (S7 s a b y z y' z' :. l+1)
            | otherwise = return Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  addIndexDenseGo _ (_:.OFirstLeft _) _ _ = error "SynVar.Indices.Subword : OFirstLeft"
  addIndexDenseGo _ (_:.OLeftOf    _) _ _ = error "SynVar.Indices.Subword : LeftOf"
  {-# Inline addIndexDenseGo #-}

-- TODO
-- @
-- Table: Inside
-- Grammar: Outside
-- @

-- |
-- @
-- Table: Complement
-- Grammar: Complement
-- @

instance
  ( AddIndexDense a us is
  , GetIndex a (is:.Subword C)
  , GetIx a (is:.Subword C) ~ (Subword C)
  ) => AddIndexDense a (us:.Subword C) (is:.Subword C) where
  addIndexDenseGo (cs:.c) (vs:.Complemented) (us:.u) (is:.i)
    = map (\(S7 s a b y z y' z') -> let k = getIndex a (Proxy :: Proxy (is:.Subword C))
                                        oo = subword 0 0
                                    in  S7 s a b (y:.k) (z:.oo) (y':.k) (z':.oo))
    . addIndexDenseGo cs vs us is
  {-# Inline addIndexDenseGo #-}

