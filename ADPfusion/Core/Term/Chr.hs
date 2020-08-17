
-- |
--
-- TODO Rename @Chr@ to @Vtx@, a vertex parser is a generalization of
-- a char parser. But this is only semantics, so not super important to do
-- now.

module ADPfusion.Core.Term.Chr where

import           Data.Strict.Tuple
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADPfusion.Core.Classes
import           ADPfusion.Core.Multi



-- | A generic Character parser that reads a single character but allows
-- passing additional information.
--
--  'Chr' expects a function to retrieve @r@ at index position, followed by
--  the actual generic vector with data.

data Chr r x where
  Chr :: VG.Vector v x
      => (v x -> Int -> r)
      -> !(v x)
      -> Chr r x

-- | smart constructor for regular 1-character parsers

chr :: VG.Vector v x => v x -> Chr x x
{-# Inline chr #-}
chr = Chr VG.unsafeIndex

-- | @Chr@ with its index. This version exposes the index, where the character @x@ is located on the
-- input vector.

chrIx :: VG.Vector v x => v x -> Chr (x,Int) x
{-# Inline chrIx #-}
chrIx xs = Chr f xs where
  {-# Inline [0] f #-}
  f xs k = (VG.unsafeIndex xs k, k)

-- | Smart constructor for Maybe Peeking, followed by a character.

chrLeft :: VG.Vector v x => v x -> Chr (Maybe x, x) x
{-# Inline chrLeft #-}
chrLeft xs = Chr f xs where
  {-# Inline [0] f #-}
  f xs k = ( xs VG.!? (k-1)
           , VG.unsafeIndex xs k
           )

chrRight :: VG.Vector v x => v x -> Chr (x, Maybe x) x
{-# Inline chrRight #-}
chrRight xs = Chr f xs where
  {-# Inline [0] f #-}
  f xs k = ( VG.unsafeIndex xs k
           , xs VG.!? (k+1)
           )

-- | Return the character at position @k@ and also the whole vector to the left of it, without
-- actually consuming the left part.

chrVecL :: VG.Vector v x => v x -> Chr (v x, x) x
{-# Inline chrVecL #-}
chrVecL xs = Chr f xs where
  {-# Inline [0] f #-}
  f xs k = ( VG.unsafeTake k xs
           , VG.unsafeIndex xs k    -- get character at position @k@
           )

chrVecR :: VG.Vector v x => v x -> Chr (x,v x) x
{-# Inline chrVecR #-}
chrVecR xs = Chr f xs where
  {-# Inline [0] f #-}
  f xs k = ( VG.unsafeIndex xs k    -- get character at position @k@
           , VG.unsafeDrop (k+1) xs
           )

-- | The fully generic chr context version, where both the full left, and full right remainder of
-- the vector are returned. The internal unsafe take/drop should be safe as long as @chrContext@ is
-- used in a legal production rule, as this will guarantee that internal indices will not be
-- out-of-bounds.

chrContext :: VG.Vector v x => v x -> Chr (v x,x,v x) x
{-# Inline chrContext #-}
chrContext xs = Chr f xs where
  {-# Inline [0] f #-}
  f xs k = ( VG.unsafeTake k xs, VG.unsafeIndex xs k, VG.unsafeDrop (k+1) xs )



instance Build (Chr r x)

instance
  ( Element ls i
  ) => Element (ls :!: Chr r x) i where
    data Elm (ls :!: Chr r x) i = ElmChr !r !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: Chr r x)   = Arg ls :. r
    type RecElm (ls :!: Chr r x) i = Elm (ls :!: Chr r x) i
    getArg (ElmChr x _ ls) = getArg ls :. x
    getIdx (ElmChr _ i _ ) = i
    getElm = id
    {-# Inline getArg #-}
    {-# Inline getIdx #-}
    {-# Inline getElm #-}

deriving instance (Show i, Show (RunningIndex i), Show r, Show (Elm ls i)) => Show (Elm (ls :!: Chr r x) i)

type instance TermArg (Chr r x) = r

