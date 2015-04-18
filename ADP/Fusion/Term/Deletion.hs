
module ADP.Fusion.Term.Deletion
  ( module ADP.Fusion.Term.Deletion.Type
  , module ADP.Fusion.Term.Deletion.Point
  ) where

import ADP.Fusion.Term.Deletion.Point
import ADP.Fusion.Term.Deletion.Type


{-
import           Data.Strict.Maybe
import           Data.Strict.Tuple
import           Prelude hiding (Maybe(..))
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray -- (Z(..), (:.)(..), Subword(..), subword, PointL(..), pointL, PointR(..), pointR)

import           ADP.Fusion.Term.Classes
import           ADP.Fusion.Term.Multi.Classes




none = None
{-# INLINE none #-}

-- | Since 'None' doesn't really do anything for all indices, we just thread it
-- through.

instance TermStaticVar None ix where
  termStaticVar   _ sv _  = sv
  termStreamIndex _ _  ij = ij
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a None) (is:.PointL) where
  terminalStream (a:|None) (sv:._) (is:._)
    = S.map (\(Qd s (z:.i) is e) -> Qd s z (is:.i) (e:.()))
    . terminalStream a sv is
    . S.map moveIdxTr
  {-# INLINE terminalStream #-}



-- * Single dimensional instances for 'None' are really weird

{-
instance Element ls Subword => Element (ls :!: None) Subword where
  data Elm (ls :!: None) Subword = ElmNone !Subword !(Elm ls Subword)
  type Arg (ls :!: None)         = Arg ls :. ()
  getArg (ElmNone _ l) = getArg l :. ()
  getIdx (ElmNone i _) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}
-}

-- | The instance does nothing (except insert @()@ into the argument
-- stack).

{-
instance
  ( Monad m
  , MkStream m ls Subword
  ) => MkStream m (ls :!: None) Subword where
  mkStream (ls :!: None) sv lu ij
    = S.map (ElmNone ij)
    $ mkStream ls sv lu ij
  {-# INLINE mkStream #-}
-}

-}

