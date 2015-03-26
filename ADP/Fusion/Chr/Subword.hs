
module ADP.Fusion.Chr.Subword where

import           Data.Strict.Tuple
import           Data.Vector.Fusion.Util (delay_inline)
import           Debug.Trace
import           Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           Prelude hiding (map)

import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Base
import           ADP.Fusion.Chr.Type



instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Chr r x) Subword where
  mkStream (ls :!: Chr f xs) IStatic hh (Subword (i:.j))
    = staticCheck (i>=0 && i<j && j<= VG.length xs)
    $ map (ElmChr (f xs $ j-1) (subword (j-1) j) (subword 0 0))
    $ mkStream ls IStatic hh (delay_inline Subword (i:.j-1))
  mkStream (ls :!: Chr f xs) IVariable hh (Subword (i:.j))
    = map (\s -> let Subword (_:.l) = getIdx s
                 in  ElmChr (f xs l) (subword l (l+1)) (subword 0 0) s)
    $ mkStream ls IVariable hh (delay_inline Subword (i:.j-1))
  {-# Inline mkStream #-}



instance
  ( Monad m
  , Element ls (Outside Subword)
  , MkStream m ls (Outside Subword)
  ) => MkStream m (ls :!: Chr r x) (Outside Subword) where
  mkStream (ls :!: Chr f xs) (OStatic (di:.dj)) u ij@(O (Subword (i:.j)))
    = id -- staticCheck ( j < h ) -- TODO any check possible?
    $ map (\s -> let (O (Subword (_:.k'))) = getIdx s
                     k = k'-dj-1
                 in  ElmChr (f xs k) (O $ subword (k'-1) k') (getOmx s) s)
    $ mkStream ls (OStatic (di:.dj+1)) u ij
  mkStream (ls :!: Chr f xs) (ORightOf (di:.dj)) u ij
    = map (\s -> let (O (Subword (_:.k'))) = getIdx s
                     k = k'-dj-1
                 in  ElmChr (f xs k) (O $ subword (k'-1) k') (getOmx s) s)
    $ mkStream ls (ORightOf (di:.dj+1)) u ij
  mkStream (ls :!: Chr f xs) (OFirstLeft (di:.dj)) u ij
    = id
    $ map (\s -> let (O (Subword (_:.k))) = getIdx s
                 in  ElmChr (f xs k) (O $ subword k (k+1)) (getOmx s) s)
    $ mkStream ls (OFirstLeft (di+1:.dj)) u ij
  mkStream (ls :!: Chr f xs) (OLeftOf (di:.dj)) u ij
    = map (\s -> let (O (Subword (_:.k))) = getIdx s
                 in  ElmChr (f xs k) (O $ subword k (k+1)) (getOmx s) s)
    $ mkStream ls (OLeftOf (di+1:.dj)) u ij
  {-# Inline mkStream #-}

