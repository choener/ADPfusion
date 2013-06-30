{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module ADP.Fusion.Multi.Classes where

import Data.Array.Repa.Index
import Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S

import ADP.Fusion.Classes



-- | The zero-th dimension of every terminal parser.

data TermBase = T

-- | Combine a terminal parser of dimension k in @a@ with a new 1-dim parser
-- @b@ generating a parser of dimension k+1.

data Term a b = a :! b

-- | A 'termStream' extracts all terminal elements from a multi-dimensional
-- terminal symbol.

class
  ( Monad m
  ) => TermElm m t ix where
  termStream :: t -> InOut ix -> ix -> S.Stream m (ze :!: zix :!: ix) -> S.Stream m (ze :!: zix :!: ix :!: TermOf t)

-- |

type family TermOf t :: *

-- | To calculate parser ranges and index validity we need an additional type
-- class that recurses over the individual 'Term' elements.

class TermValidIndex t i where
  termDimensionsValid :: t -> ParserRange i -> i -> Bool
  getTermParserRange  :: t -> i -> ParserRange i -> ParserRange i
  termInnerOuter :: t -> i -> InOut i -> InOut i
  termLeftIndex :: t -> i -> i



-- * The instance declarations for generic @Term a b@ data ctors.

instance Build (Term a b)

instance
  ( ValidIndex ls ix
  , TermValidIndex (Term a b) ix
  , Show ix
  , Show (ParserRange ix)
  ) => ValidIndex (ls :!: Term a b) ix where
  validIndex (ls :!: t) abc ix =
    termDimensionsValid t abc ix && validIndex ls abc ix
  {-# INLINE validIndex #-}
  getParserRange (ls :!: t) ix = getTermParserRange t ix (getParserRange ls ix)
  {-# INLINE getParserRange #-}

instance
  ( Elms ls ix
  ) => Elms (ls :!: Term a b) ix where
    data Elm (ls :!: Term a b) ix = ElmTerm !(Elm ls ix) !(TermOf (Term a b)) !ix
    type Arg (ls :!: Term a b) = Arg ls :. (TermOf (Term a b))
    getArg !(ElmTerm ls x _) = getArg ls :. x
    getIdx !(ElmTerm _ _ idx) = idx
    {-# INLINE getArg #-}
    {-# INLINE getIdx #-}

instance
  ( Monad m
  , Elms ls ix
  , MkStream m ls ix
  , TermElm m (Term a b) ix
  , TermValidIndex (Term a b) ix
  ) => MkStream m (ls :!: Term a b) ix where
  mkStream !(ls :!: t) !io !ij
    = S.map (\(s:!:Z:!:zij:!:e) -> ElmTerm s e zij)
    $ termStream t io ij
    $ S.map (\s -> (s :!: Z :!: getIdx s))
    $ mkStream ls (termInnerOuter t ij io) (termLeftIndex t ij)
  {-# INLINE mkStream #-}



-- * Terminal stream of 'TermBase' with index 'Z'

type instance TermOf TermBase = Z

instance
  ( Monad m
  ) => TermElm m (TermBase) Z where
  termStream T _ Z = S.map (\(zs:!:zix:!:Z) -> (zs:!:zix:!:Z:!:Z))
  {-# INLINE termStream #-}

instance TermValidIndex TermBase Z where
  termDimensionsValid T Z Z = True
  getTermParserRange  T Z Z = Z
  termInnerOuter T Z Z = Z
  termLeftIndex T Z = Z
  {-# INLINE termDimensionsValid #-}
  {-# INLINE getTermParserRange #-}
  {-# INLINE termInnerOuter #-}
  {-# INLINE termLeftIndex #-}

