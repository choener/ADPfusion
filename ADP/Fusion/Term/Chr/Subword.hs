
module ADP.Fusion.Term.Chr.Subword where

import           Data.Strict.Tuple
import           Data.Vector.Fusion.Util (delay_inline)
import           Debug.Trace
import           Data.Vector.Fusion.Stream.Monadic as S
import qualified Data.Vector.Generic as VG
import           Prelude hiding (map)

import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Base
import           ADP.Fusion.Term.Chr.Type



instance
  ( Monad m
  , Element ls Subword
  , MkStream m ls Subword
  ) => MkStream m (ls :!: Chr r x) Subword where
  mkStream (ls :!: Chr f xs) (IStatic ()) hh (Subword (i:.j))
    = staticCheck (i>=0 && i<j && j<= VG.length xs)
    $ map (ElmChr (f xs $ j-1) (subword (j-1) j) (subword 0 0))
    $ mkStream ls (IStatic ()) hh (delay_inline Subword (i:.j-1))
  mkStream (ls :!: Chr f xs) (IVariable ()) hh (Subword (i:.j))
    = map (\s -> let Subword (_:.l) = getIdx s
                 in  ElmChr (f xs l) (subword l (l+1)) (subword 0 0) s)
    $ mkStream ls (IVariable ()) hh (delay_inline Subword (i:.j-1))
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



instance
  ( Monad m
  , TerminalStream m a is
  ) => TerminalStream m (TermSymbol a (Chr r x)) (is:.Subword) where
  terminalStream (a:|Chr f v) (sv:.IStatic _) (is:.ix@(Subword (i:.j)))
    -- TODO check if 'staticCheck' breaks fusion!!!
    = staticCheck (i>=0 && i<j && j<=VG.length v)
    . S.map (\(S6 s (zi:._) (zo:._) is os e) -> S6 s zi zo (is:.subword (j-1) j) (os:.subword 0 0) (e:.f v (j-1)))
    . iPackTerminalStream a sv (is:.ix)
  terminalStream (a:|Chr f v) (sv:.IVariable _) (is:.ix@(Subword (i:.j)))
    = S.map (\(S6 s (zi:.Subword (_:.l)) (zo:._) is os e) -> S6 s zi zo (is:.subword l (l+1)) (os:.subword 0 0) (e:.f v l))
    . iPackTerminalStream a sv (is:.ix)
  {-# Inline terminalStream #-}

instance TermStaticVar (Chr r x) Subword where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (Subword (i:.j)) = subword i (j-1)
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}

