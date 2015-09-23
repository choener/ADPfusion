
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
    :: (Monad m)
    => TblConstraint u -> Context i -> i -> i -> Stream m (SvState s a Z Z) -> Stream m (SvState s a u i)

instance AddIndexDense a Z Z where
  addIndexDenseGo _ _ _ _ = id
  {-# Inline addIndexDenseGo #-}

-- | @SvState@ holds the state that is currently being built up by
-- @AddIndexDense@. We have both @tIx@ (and @tOx@) and @iIx@ (and @iOx@).
-- For most index structures, the indices will co-incide; however for some,
-- this will not be true -- herein for @Set@ index structures.

data SvState s a u i = SvS
  { sS  :: !s -- | state coming in from the left
  , sIx :: !a -- | @I/C@ index from @sS@
  , sOx :: !a -- | @O@ index from @sS@
  , tx  :: !u -- | @I/C@ building up state to index the @table@.
  , iIx :: !i -- | @I/C@ building up state to hand over to next symbol
  , iOx :: !i -- | @O@ building up state to hand over to next symbol
  }


-- | Given an incoming stream with indices, this adds indices for the
-- current syntactic variable / symbol.

addIndexDense
  :: ( Monad m
     , AddIndexDense a u i
     , GetIndex a i
     , s ~ Elm x0 a
     , Element x0 a
     )
  => TblConstraint u -> Context i -> i -> i -> Stream m s -> Stream m (s,u,i,i)
addIndexDense t c u i = map (\(SvS s _ _ z i' o') -> (s,z,i',o')) . addIndexDenseGo t c u i . map (\s -> (SvS s (getIdx s) (getOmx s) Z Z Z))
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
  => TblConstraint u -> Context i -> i -> i -> Stream m s -> Stream m (s,u,i,i)
addIndexDense1 t c u i = map (\(SvS s _ _ (Z:.z) (Z:.i') (Z:.o')) -> (s,z,i',o'))
                       . addIndexDenseGo (Z:.t) (Z:.c) (Z:.u) (Z:.i)
                       . map (\s -> (SvS s (Z:.getIdx s) (Z:.getOmx s) Z Z Z))
{-# Inline addIndexDense1 #-}

