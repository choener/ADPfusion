
module ADP.Fusion.Base.Term where

import Data.Vector.Fusion.Stream.Monadic

import Data.PrimitiveArray

import ADP.Fusion.Base.Classes
import ADP.Fusion.Base.Multi



data TermState s a u i e = TState
  { sS  :: !s -- | state coming in from the left
  , sIx :: !a -- | @I/C@ index from @sS@
  , sOx :: !a -- | @O@ index from @sS@
--  , tt  :: !u -- | @I/C@ building up state to index the @table@.
  , iIx :: !i -- | @I/C@ building up state to hand over to next symbol
  , iOx :: !i -- | @O@ building up state to hand over to next symbol
  , eTS :: !e -- | element data
  }

class TermStream m t u i where
  termStream :: t -> i -> i -> Stream m (TermState s a Z Z Z) -> Stream m (TermState s a u i (TermArg t))

instance TermStream m M Z Z where
  termStream _ _ _ = id
  {-# Inline termStream #-}

