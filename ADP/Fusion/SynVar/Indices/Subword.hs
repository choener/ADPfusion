
-- | Instance code for @Inside@, @Outside@, and @Complement@ indices.
--
-- TODO actual @Outside@ and @Complement@ code ...

module ADP.Fusion.SynVar.Indices.Subword where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,flatten,Step(..))
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util (delay_inline)
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Indices.Classes



instance
  ( AddIndexDense a us is
  , GetIndex a (is:.Subword)
  , GetIx a (is:.Subword) ~ Subword
  ) => AddIndexDense a (us:.Subword) (is:.Subword) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:.Subword (_:.u)) (is:.Subword (i:.j))
    = staticCheck (j<=u)
    . map (\(S7 s a b y z y' z') -> let (Subword (_:.l)) = getIndex a (Proxy :: Proxy (is:.Subword))
                                        lj = subword l j
                                        oo = subword 0 0
                                    in  S7 s a b (y:.lj) (z:.oo) (y':.lj) (z':.oo))
    . addIndexDenseGo cs vs us is
  addIndexDenseGo (cs:.c) (vs:.IVariable ()) (us:.Subword (_:.u)) (is:.Subword (i:.j))
    = staticCheck (j<=u)
    . flatten mk step Unknown . addIndexDenseGo cs vs us is
    where mk   (S7 s a b y z y' z') = let (Subword (_:.l)) = getIndex a (Proxy :: Proxy (is:.Subword))
                                      in  return $ S8 s a b y z y' z' (j - l - csize)
          step (S8 s a b y z y' z' zz)
            | zz >= 0 = do let Subword (_:.k) = getIndex a (Proxy :: Proxy (is:.Subword))
                               l = j - zz ; kl = subword k l
                               oo = subword 0 0
                           return $ Yield (S7 s a b (y:.kl) (z:.oo) (y':.kl) (z':.oo)) (S8 s a b y z y' z' (zz-1))
            | otherwise =  return $ Done
          csize = delay_inline minSize c
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

