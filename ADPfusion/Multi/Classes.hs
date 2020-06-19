
module ADPfusion.Multi.Classes where


import           Data.PrimitiveArray -- (Z(..), (:.)(..), Subword(..), subword, PointL(..), pointL, PointR(..), pointR)

import           ADPfusion.Classes



--type instance TermArg (TermSymbol a b) = TermArg a :. b

{-
instance (Monad m, MkStream m S is) => MkStream m S (is:.Subword) where
  mkStream S (vs:.Static) (lus:.lu) (is:.Subword (i:.j))
    = staticCheck (i==j)
    . S.map (\(ElmS z) -> ElmS (z:.subword i i))
    $ mkStream S vs lus is
  mkStream S (vs:.Variable NoCheck Nothing) (lus:.lu) (is:.Subword (i:.j))
    = S.map (\(ElmS z) -> ElmS (z:.subword i i))
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}
-}

instance (Monad m, MkStream m S is) => MkStream m S (is:.PointR) where
  mkStream S (vs:.Static) (lus:.lu) (is:.PointR (i:.j))
    = staticCheck (i==j)
    . S.map (\(ElmS z) -> ElmS (z:.pointR i i))
    $ mkStream S vs lus is
  mkStream _ _ _ _ = error "ADP/Fusion/Multi/Classes.hs :: MkStream S/is:.PointR :: not implemented yet"
  {-# INLINE mkStream #-}

-- |

{-
instance TableStaticVar Subword where
  tableStaticVar     _ _                = error "Multi/Classes.hs :: tableStaticVar/Subword :: fixme" -- Variable NoCheck Nothing -- maybe we need a check if the constraint is 'NonEmpty' ?
  tableStreamIndex c _ (Subword (i:.j))
    | c==EmptyOk  = subword i j
    | c==NonEmpty = subword i $ j-1
    | c==OnlyZero = subword i j -- this should then actually request a size in 'tableStaticVar' ...
  {-# INLINE tableStaticVar   #-}
  {-# INLINE tableStreamIndex #-}
-}

-- |
--
-- TODO the point of promoting anything to @Variable Check Nothing@ is to have
-- a sanity check in @mkStream@ above. There we check if @i<=j@ which should
-- always be ok for the table on the left-most position of our symbols (on the
-- RHS).

moveIdxTr :: Triple a b (cs:.c) -> Triple a (b:.c) cs
moveIdxTr (Tr a b (cs:.c)) = Tr a (b:.c) cs
{-# INLINE moveIdxTr #-}

data Pen    a b c d e = Pn !a !b !c !d !e

