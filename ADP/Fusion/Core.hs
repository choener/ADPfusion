
-- | Generalized fusion system for grammars.
--
-- This module re-exports only the core functionality (and Unit indices).
--
-- NOTE Symbols typically do not check bound data for consistency. If you, say,
-- bind a terminal symbol to an input of length 0 and then run your grammar,
-- you probably get errors, garbled data or random crashes. Such checks are
-- done via asserts in non-production code.

module ADP.Fusion.Core
  ( module ADP.Fusion.Core
  , module ADP.Fusion.Apply
  , module ADP.Fusion.Base.Classes
  , module ADP.Fusion.Base.Multi
  , module ADP.Fusion.Base.TyLvlIx
  , module ADP.Fusion.Base.Unit
  , module ADP.Fusion.SynVar.Array.Type
  , module ADP.Fusion.SynVar.Axiom
  , module ADP.Fusion.SynVar.Backtrack
  , module ADP.Fusion.SynVar.Fill
  , module ADP.Fusion.SynVar.Indices.Classes
  , module ADP.Fusion.SynVar.Recursive.Type
  , module ADP.Fusion.SynVar.Split.Type
  , module ADP.Fusion.SynVar.TableWrap
  , module ADP.Fusion.Term.Chr.Type
  , module ADP.Fusion.Term.Deletion.Type
  , module ADP.Fusion.Term.Edge.Type
  , module ADP.Fusion.Term.Epsilon.Type
  , module ADP.Fusion.Term.PeekIndex.Type
  , module ADP.Fusion.Term.Strng.Type
  , module ADP.Fusion.TH
  ) where

import           Data.Strict.Tuple
import           GHC.Exts (inline)
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray

import           ADP.Fusion.Apply
import           ADP.Fusion.Base.Classes hiding (iIx)
import           ADP.Fusion.Base.Multi hiding (iIx)
import           ADP.Fusion.Base.TyLvlIx
import           ADP.Fusion.Base.Unit
import           ADP.Fusion.SynVar.Array.Type
import           ADP.Fusion.SynVar.Axiom
import           ADP.Fusion.SynVar.Backtrack
import           ADP.Fusion.SynVar.Fill
import           ADP.Fusion.SynVar.Indices.Classes
import           ADP.Fusion.SynVar.Recursive.Type
import           ADP.Fusion.SynVar.Split.Type
import           ADP.Fusion.SynVar.TableWrap
import           ADP.Fusion.Term.Chr.Type
import           ADP.Fusion.Term.Deletion.Type
import           ADP.Fusion.Term.Edge.Type
import           ADP.Fusion.Term.Epsilon.Type
import           ADP.Fusion.Term.PeekIndex.Type
import           ADP.Fusion.Term.Strng.Type
import           ADP.Fusion.TH



-- | Apply a function to symbols on the RHS of a production rule. Builds the
-- stack of symbols from 'xs' using 'build', then hands this stack to
-- 'mkStream' together with the initial 'iniT' telling 'mkStream' that we are
-- in the "outer" position. Once the stream has been created, we 'S.map'
-- 'getArg' to get just the arguments in the stack, and finally 'apply' the
-- function 'f'.

infixl 8 <<<
(<<<) f xs = \lu ij -> S.map (apply (inline f) . getArg) . mkStream (build xs) (initialContext ij) lu $ ij
{-# INLINE (<<<) #-}

infixl 8 <<#
(<<#) f xs = \lu ij -> S.mapM (apply (inline f) . getArg) . mkStream (build xs) (initialContext ij) lu $ ij
{-# INLINE (<<#) #-}

-- | Combine two RHSs to give a choice between parses.

infixl 7 |||
(|||) xs ys = \lu ij -> xs lu ij S.++ ys lu ij
{-# INLINE (|||) #-}

-- | Applies the objective function 'h' to a stream 's'. The objective function
-- reduces the stream to a single optimal value (or some vector of co-optimal
-- things).

infixl 5 ...
(...) s h = \lu ij -> (inline h) $ s lu ij
{-# INLINE (...) #-}

-- -- | Additional outer check with user-given check function
-- 
-- infixl 6 `check`
-- check xs f = \ij -> let chk = f ij in chk `seq` outerCheck chk (xs ij)
-- {-# INLINE check #-}

-- | Separator between RHS symbols.

infixl 9 ~~
(~~) = (:!:)
{-# INLINE (~~) #-}

-- | This separator looks much paper "on paper" and is not widely used otherwise.

infixl 9 %
(%) = (:!:)
{-# INLINE (%) #-}

