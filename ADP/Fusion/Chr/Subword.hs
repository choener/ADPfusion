
module ADP.Fusion.Chr.Subword where

import           Data.Strict.Tuple
import           Data.Vector.Fusion.Util (delay_inline)
import           Debug.Trace
import qualified Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG

import           Data.PrimitiveArray

import           ADP.Fusion.Base
import           ADP.Fusion.Chr.Type


instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Chr r x) Subword where
  mkStream (ls :!: Chr f xs) IStatic hh (Subword (i:.j))
    = staticCheck (i>=0 && i<j && j<= VG.length xs)
    $ S.map (ElmChr (f xs $ j-1) (subword (j-1) j) (subword 0 0))
    $ mkStream ls IStatic hh (delay_inline subword i (j-1))
  mkStream (ls :!: Chr f xs) IVariable hh (Subword (i:.j))
    = S.map (\s -> let Subword (_:.l) = getIdx s
                   in  ElmChr (f xs l) (subword l (l+1)) (subword 0 0) s)
    $ mkStream ls IVariable hh (delay_inline subword i (j-1))
  {-# Inline mkStream #-}

