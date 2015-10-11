
{-# Options_GHC -O0 #-}

module QuickCheck.Common where

import Debug.Trace



tr zs ls b = traceShow (zs," ",ls,length zs,length ls) b
