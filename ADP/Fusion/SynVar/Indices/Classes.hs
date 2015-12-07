
-- | Classes that enumerate the index structure necessary for actually
-- performing the indexing.
--
-- TODO Currently, we only provide dense index generation.

module ADP.Fusion.SynVar.Indices.Classes where

import Data.Proxy (Proxy(..))
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,flatten,Step(..))
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base



-- | This type classes enable enumeration both in single- and multi-dim
-- cases. The type @a@ is the type of the /full stack/ of indices, i.e. the
-- full multi-tape problem.

class AddIndexDense a u c i where
  addIndexDenseGo
    :: (Monad m)
    => c -> Context i -> i -> i -> Stream m (SvState s a Z Z) -> Stream m (SvState s a u i)

instance AddIndexDense a Z Z Z where
  addIndexDenseGo _ _ _ _ = id
  {-# Inline addIndexDenseGo #-}

-- | @SvState@ holds the state that is currently being built up by
-- @AddIndexDense@. We have both @tIx@ (and @tOx@) and @iIx@ (and @iOx@).
-- For most index structures, the indices will co-incide; however for some,
-- this will not be true -- herein for @Set@ index structures.

data SvState s a u i = SvS
  { sS  :: !s -- | state coming in from the left
  , sIx :: !(RunningIndex a) -- | @I/C@ index from @sS@
  , tx  :: !u -- | @I/C@ building up state to index the @table@.
  , iIx :: !(RunningIndex i) -- | @I/C@ building up state to hand over to next symbol
  }


-- | Given an incoming stream with indices, this adds indices for the
-- current syntactic variable / symbol.

addIndexDense
  :: ( Monad m
     , AddIndexDense a u c i
     , GetIndex a i
     , s ~ Elm x0 a
     , Element x0 a
     )
  => c -> Context i -> i -> i -> Stream m s -> Stream m (s,u,RunningIndex i)
addIndexDense t c u i = map (\(SvS s _ z i') -> (s,z,i')) . addIndexDenseGo t c u i . map (\s -> (SvS s (getIdx s) Z RiZ))
{-# Inline addIndexDense #-}

-- | In case of 1-dim tables, we wrap the index creation in a multi-dim
-- system and remove the @Z@ later on. This allows us to have to write only
-- a single instance.

addIndexDense1
  :: ( Monad m
     , AddIndexDense (Z:.a) (Z:.u) (Z:.c) (Z:.i)
     , GetIndex (Z:.a) (Z:.i)
     , s ~ Elm x0 a
     , Element x0 a
     )
  => c -> Context i -> i -> i -> Stream m s -> Stream m (s,u,RunningIndex i)
addIndexDense1 t c u i = map (\(SvS s _ (Z:.z) (RiZ:.:i')) -> (s,z,i'))
                       . addIndexDenseGo (Z:.t) (Z:.c) (Z:.u) (Z:.i)
                       . map (\s -> (SvS s (RiZ :.: getIdx s) Z RiZ))
{-# Inline addIndexDense1 #-}

-- | Instance headers, we typically need.

type IndexHdr a us u cs c is i =
  ( AddIndexDense a us cs is
  , GetIndex (RunningIndex a) (RunningIndex (is:.i))
  , GetIx (RunningIndex a) (RunningIndex (is:.i)) ~ (RunningIndex i)
  )

