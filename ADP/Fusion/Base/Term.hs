
module ADP.Fusion.Base.Term where

import Data.Vector.Fusion.Stream.Monadic
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



data TermState s a i e = TState
  { sS  :: !s -- | state coming in from the left
  , sIx :: !a -- | @I/C@ index from @sS@
  , sOx :: !a -- | @O@ index from @sS@
--  , tt  :: !u -- | @I/C@ building up state to index the @table@.
  , iIx :: !i -- | @I/C@ building up state to hand over to next symbol
  , iOx :: !i -- | @O@ building up state to hand over to next symbol
  , eTS :: !e -- | element data
  }

class TermStream m t a i where
  termStream :: t -> Context i -> i -> i -> Stream m (TermState s a Z Z) -> Stream m (TermState s a i (TermArg t))

instance TermStream m M a Z where
  termStream _ _ _ _ = id
  {-# Inline termStream #-}

-- |
--
-- TODO need @t -> ElmType t@ type function
--
-- TODO need to actually return an @ElmType t@ can do that instead of
-- returning @u@ !!!

addTermStream1
  :: ( Monad m
     , TermStream m (TermSymbol M t) (Z:.a) (Z:.i)
     , s ~ Elm x0 a
     , Element x0 a
     )
  => t -> Context i -> i -> i -> Stream m s -> Stream m (s,TermArg t,i,i)
addTermStream1 t c u i
  = map (\(TState sS _ _ (Z:.ii) (Z:.oo) (Z:.ee)) -> (sS,ee,ii,oo))
  . termStream (M:|t) (Z:.c) (Z:.u) (Z:.i)
  . map (\s -> TState s (Z:.getIdx s) (Z:.getOmx s) Z Z Z)
{-# Inline addTermStream1 #-}

