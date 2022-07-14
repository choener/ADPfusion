
-- | Classes that enumerate the index structure necessary for actually
-- performing the indexing.
--
-- TODO Currently, we only provide dense index generation.

module ADPfusion.Core.SynVar.Indices where

import Data.Proxy (Proxy(..))
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,flatten,Step(..))
import Prelude hiding (map,head,mapM)
import Data.Void

import Data.PrimitiveArray hiding (map)

import ADPfusion.Core.Classes
import ADPfusion.Core.Multi
import ADPfusion.Core.TyLvlIx



-- | This type class enables enumeration both in single- and multi-dim
-- cases. The type @a@ is the type of the /full stack/ of indices, i.e. the
-- full multi-tape problem.
--
-- @pos@ is the positional information,
-- @s@ is the element type over the index @ix@,
-- @ minSize@ the minimal size or width to request from the syntactic variable,
-- @tableIx@ the index type of the table to walk over,
-- and @ix@ the actual index.

class AddIndexDense pos elm minSize tableIx ix where
  addIndexDenseGo
    :: (Monad m)
    => Proxy pos
    -- ^ Positional information in the rule (static/variable/etc)
    -> minSize
    -- ^ Minimal size of the structure under consideration. We might want to
    -- constrain enumeration over syntactic variables to only consider at least
    -- "size>=1" cases. Normally, a syntactic variable may be of size 0 as
    -- well, but with rules like @X -> X X@, we don't want to have one of the
    -- @X@'s on the r.h.s. be of size 0.
    -> LimitType tableIx
    -- ^ The upper limit imposed by the structure to traverse over.
    -> LimitType ix
    -- ^ The upper limit imposed by the rule that traverses.
    -> ix
    -- ^ The current index for the full rule.
    -> Stream m (SvState elm Z Z)
    -- ^ Initial stream state with @Z@ero indices.
    -> Stream m (SvState elm tableIx ix)
    -- ^ The type of the full stream.

instance AddIndexDense pos elm Z Z Z where
  addIndexDenseGo _ _ _ _ _ = id
  {-# Inline addIndexDenseGo #-}

-- | @SvState@ holds the state that is currently being built up by
-- @AddIndexDense@. We have both @tIx@ (and @tOx@) and @iIx@ (and @iOx@).
-- For most index structures, the indices will co-incide; however for some,
-- this will not be true -- herein for @Set@ index structures.

data SvState elm tableIx ix = SvS
  { sS  :: !elm
  -- ^ state coming in from the left
  , tx  :: !tableIx
  -- ^ @I/C@ building up state to index the @table@.
  , iIx :: !(RunningIndex ix)
  -- ^ @I/C@ building up state to hand over to next symbol
  }


-- | Given an incoming stream with indices, this adds indices for the
-- current syntactic variable / symbol.

addIndexDense
  :: ( Monad m
    , AddIndexDense pos elm minSize tableIx ix
    , elm ~ Elm x0 i0
    , Element x0 i0
    )
  => Proxy pos
  -> minSize
  -> LimitType tableIx
  -> LimitType ix
  -> ix
  -> Stream m elm
  -> Stream m (elm,tableIx,RunningIndex ix)
addIndexDense pos minSize tableBound upperBound ix
  = map (\(SvS s z i') -> (s,z,i'))
  . addIndexDenseGo pos minSize tableBound upperBound ix
  . map (\s -> (SvS s Z RiZ))
{-# Inline addIndexDense #-}

-- | In case of 1-dim tables, we wrap the index creation in a multi-dim
-- system and remove the @Z@ later on. This allows us to have to write only
-- a single instance.

addIndexDense1
  :: forall m pos x0 a ix minSize tableIx elm
  . ( Monad m
    , AddIndexDense (Z:.pos) (Elm (SynVar1 (Elm x0 a)) (Z:.ix)) (Z:.minSize) (Z:.tableIx) (Z:.ix)
    , GetIndex (Z:.a) (Z:.ix)
    , elm ~ Elm x0 a
    , Element x0 a
    )
  => Proxy pos
  -> minSize
  -> LimitType tableIx
  -> LimitType ix
  -> ix
  -> Stream m elm
  -> Stream m (elm,tableIx,RunningIndex ix)
addIndexDense1 Proxy minSize tableBound upperBound ix
  = map (\(SvS (ElmSynVar1 s) (Z:.z) (RiZ:.:i')) -> (s,z,i'))
  . addIndexDenseGo (Proxy :: Proxy (Z:.pos)) (Z:.minSize) (ZZ:..tableBound) (ZZ:..upperBound) (Z:.ix)
  . map (\s -> (SvS (elmSynVar1 s ix) Z RiZ))
{-# Inline addIndexDense1 #-}

newtype SynVar1 s = SynVar1 s

elmSynVar1 :: s -> i -> Elm (SynVar1 s) (Z:.i)
elmSynVar1 s _ = ElmSynVar1 s
{-# Inline elmSynVar1 #-}

instance (s ~ Elm x0 i, Element x0 i) => Element (SynVar1 s) (Z:.i) where
  newtype Elm (SynVar1 s) (Z:.i) = ElmSynVar1 s
  type Arg (SynVar1 s) = Void
  type RecElm (SynVar1 s) (Z:.i) = Void
  getIdx (ElmSynVar1 s) = RiZ :.: getIdx s
  getArg = error "wrapper: not required"
  getElm = error "wrapper: not required"
  {-# Inline getIdx #-}


-- | Instance headers, we typically need.

type AddIndexDenseContext pos elm x0 i0 minSizes minSize tableIxs tableIx ixs ix =
  ( AddIndexDense pos elm minSizes tableIxs ixs
  , GetIndex (RunningIndex i0) (RunningIndex (ixs:.ix))
  , GetIx (RunningIndex i0) (RunningIndex (ixs:.ix)) ~ (RunningIndex ix)
  , Element x0 i0
  , elm ~ Elm x0 i0
  )

