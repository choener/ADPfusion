
-- | Classes that enumerate the index structure necessary for actually
-- performing the indexing.
--
-- TODO Currently, we only provide dense index generation.

module ADP.Fusion.SynVar.Indices.Classes where

import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,flatten,Step(..))
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base



-- | This type classes enable enumeration both in single- and multi-dim
-- cases. The type @a@ is the type of the /full stack/ of indices, i.e. the
-- full multi-tape problem.


class AddIndexDense a u i where
  addIndexDenseGo
    :: (Monad m) -- , GetIndex a i)
    => TblConstraint u -> Context i -> i -> i -> Stream m (S7 s a a Z Z Z Z) -> Stream m (S7 s a a u u i i)

instance AddIndexDense a Z Z where
  addIndexDenseGo _ _ _ _ = id
  {-# Inline addIndexDenseGo #-}



-- | Given an incoming stream with indices, this adds indices for the
-- current syntactic variable / symbol.

addIndexDense
  :: ( Monad m
     , AddIndexDense a u i
     , GetIndex a i
     , s ~ Elm x0 a
     , Element x0 a
     )
  => TblConstraint u -> Context i -> i -> i -> Stream m s -> Stream m (s,u,u,i,i)
addIndexDense t c u i = map (\(S7 s _ _ i o i' o') -> (s,i,o,i',o')) . addIndexDenseGo t c u i . map (\s -> (S7 s (getIdx s) (getOmx s) Z Z Z Z))
{-# Inline addIndexDense #-}

-- | In case of 1-dim tables, we wrap the index creation in a multi-dim
-- system and remove the @Z@ later on. This allows us to have to write only
-- a single instance.

addIndexDense1
  :: ( Monad m
     , AddIndexDense (Z:.a) (Z:.u) (Z:.i)
     , GetIndex (Z:.a) (Z:.i)
     , s ~ Elm x0 a
     , Element x0 a
     )
  => TblConstraint u -> Context i -> i -> i -> Stream m s -> Stream m (s,u,u,i,i)
addIndexDense1 t c u i = map (\(S7 s _ _ (Z:.i) (Z:.o) (Z:.i') (Z:.o')) -> (s,i,o,i',o')) . addIndexDenseGo (Z:.t) (Z:.c) (Z:.u) (Z:.i) . map (\s -> (S7 s (Z:.getIdx s) (Z:.getOmx s) Z Z Z Z))
{-# Inline addIndexDense1 #-}

