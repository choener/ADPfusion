
-- | Instance code for @Inside@, @Outside@, and @Complement@ indices.
--
-- TODO actual @Outside@ and @Complement@ code ...

module ADP.Fusion.SynVar.Indices.Subword where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,flatten,Step(..))
import Data.Vector.Fusion.Stream.Size
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



instance
  ( AddIndexDense a is
  , GetIndex a is
  , GetIx a (is:.Subword) ~ Subword
  ) => AddIndexDense a (is:.Subword) where
  addIndexDenseGo (cs:.c) (vs:.IStatic ()) (is:.Subword (i:.j))
    = map (\(S5 s a b y z) -> let (Subword (_:.l)) = getIndex a (Proxy :: Proxy (is:.Subword))
                              in  (S5 s a b (y:.subword l j) (z:.subword 0 0)))
    . addIndexDenseGo cs vs is
  addIndexDenseGo (cs:.c) (vs:.IVariable ()) (is:.Subword (i:.j))
    = flatten mk step Unknown . addIndexDenseGo cs vs is
    where mk   (S5 s a b y z) = let (Subword (_:.l)) = getIndex a (Proxy :: Proxy (is:.Subword)) in return $ S6 s a b y z (j - l - minSize c)
          step (S6 s a b y z zz)
            | zz >= 0 = do let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword))
                               l = j - zz ; kl = subword k l
                           return $ Yield (S5 s a b (y:.kl) (z:.subword 0 0)) (S6 s a b y z (zz-1))
            | otherwise = return $ Done
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}


{-

testAddIndex i j =
  let (_,(_:.Subword (a:.b):.Subword (c:.d)),_) = S.head
                                                $ addIndex (Z:.EmptyOk:.EmptyOk) (Z:.IStatic():.IVariable ()) (Z:.subword i (2*i):.subword j (3*j))
                                                $ S.singleton
                                                $ ElmS (Z:.subword (4*i) (5*i):.subword (6*j) (7*j)) (Z:.subword 0 0:.subword 0 0)
  in  (a,b,c,d)
{-# NoInline testAddIndex #-}

testAddIndexLen i j
  = S.length
  $ addIndex (Z:.EmptyOk:.EmptyOk) (Z:.IVariable():.IVariable ()) (Z:.subword i (2*i):.subword j (3*j))
  $ S.singleton
  $ ElmS (Z:.subword (4*i) (5*i):.subword (6*j) (7*j)) (Z:.subword 0 0:.subword 0 0)
{-# NoInline testAddIndexLen #-}

testAddIndex1 i j =
  let (_,(Subword (a:.b)),_) = S.head
                             $ addIndex1 EmptyOk (IVariable ()) (subword i j)
                             $ S.singleton
                             $ ElmS (subword i j) (subword 0 0)
  in  (a,b)
{-# NoInline testAddIndex1 #-}

-}

