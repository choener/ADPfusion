
-- | 'Switch'es allow enabling and disabling individual rules on a global
-- level.
--
-- TODO Consider moving the switch status to the type level.
-- TODO Consider using patterns for the switch status and encode using @Int@s.

module ADPfusion.Core.Term.Switch where

import           Data.Strict.Tuple
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADPfusion.Core.Classes
import           ADPfusion.Core.Multi



-- | Explicit naming of the status of the switch.

data SwitchStatus = Disabled | Enabled
  deriving (Eq,Ord,Show)

-- | Terminal for the switch. The switch status is not given to any function,
-- since processing of the rule already indicates that the switch is enabled --
-- if all other symbols parse successfully. Due to consistency, the type of
-- result is @()@.

data Switch where
  Switch ∷ !SwitchStatus → Switch

instance Build Switch

instance
  ( Element ls i
  ) => Element (ls :!: Switch) i where
    data Elm (ls :!: Switch) i = ElmSwitch !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: Switch)   = Arg ls :. ()
    type RecElm (ls :!: Switch) i = Elm (ls :!: Switch) i
    getArg (ElmSwitch _ ls) = getArg ls :. ()
    getIdx (ElmSwitch i _ ) = i
    getElm = id
    {-# Inline getArg #-}
    {-# Inline getIdx #-}
    {-# Inline getElm #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: Switch) i)

type instance TermArg Switch = ()

