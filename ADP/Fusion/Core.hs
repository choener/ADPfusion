
{-# Language MagicHash #-}

-- | Generalized fusion system for grammars.
--
-- This module re-exports only the core functionality.
--
-- NOTE Symbols typically do not check bound data for consistency. If you, say,
-- bind a terminal symbol to an input of length 0 and then run your grammar,
-- you probably get errors, garbled data or random crashes. Such checks are
-- done via asserts in non-production code.

module ADP.Fusion.Core
  ( module ADP.Fusion.Core
  , module ADP.Fusion.Core.Apply
  , module ADP.Fusion.Core.Classes
  , module ADP.Fusion.Core.Multi
  , module ADP.Fusion.Core.TH
  , module ADP.Fusion.Core.TyLvlIx
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
  , module Data.Vector.Fusion.Stream.Monadic
  , module Data.Vector.Fusion.Util
  ) where

import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import           Data.Strict.Tuple
import           GHC.Exts (inline)
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           Data.Vector.Fusion.Util (Id(..))

import           Data.PrimitiveArray

import           ADP.Fusion.Core.Apply
import           ADP.Fusion.Core.Classes hiding (iIx)
import           ADP.Fusion.Core.Multi hiding (iIx)
import           ADP.Fusion.Core.TH
import           ADP.Fusion.Core.TyLvlIx
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



-- | Apply a function to symbols on the RHS of a production rule. Builds the
-- stack of symbols from 'xs' using 'build', then hands this stack to
-- 'mkStream' together with the initial 'iniT' telling 'mkStream' that we are
-- in the "outer" position. Once the stream has been created, we 'S.map'
-- 'getArg' to get just the arguments in the stack, and finally 'apply' the
-- function 'f'.

infixl 8 <<<
(<<<)
  ∷ forall m symbols i b
  . ( Monad m
    , Build symbols
    , Element (Stack symbols) i
    , Apply (Arg (Stack symbols) → b)
    , MkStream m (InitialContext i) (Stack symbols) i
    , RuleContext i
    )
  ⇒ (Fun (Arg (Stack symbols) → b))
  → symbols
  → (LimitType i → i → Stream m b)
(<<<) f xs
  = \lu ij
  → S.map (apply (inline f) . getArg)
  $ mkStream (initialContext (Proxy ∷ Proxy i)) (build xs) 1# lu ij
{-# INLINE (<<<) #-}

--infixl 8 <<#
--(<<#) f xs = \lu ij -> S.mapM (apply (inline f) . getArg) $ mkStream Proxy (build xs) 1# lu ij
--{-# INLINE (<<#) #-}

-- | Combine two RHSs to give a choice between parses.

infixl 7 |||
(|||) xs ys = \lu ij -> xs lu ij `streamappend` ys lu ij
{-# INLINE (|||) #-}

data StreamAppend a b = SAL a | SAR b

streamappend :: Monad m => Stream m a -> Stream m a -> Stream m a
{-# Inline [1] streamappend #-}
Stream stepa ta `streamappend` Stream stepb tb = Stream step (SAL ta)
  where
    {-# Inline [0] step #-}
    step (SAL   sa) = do
                        r <- stepa sa
                        case r of
                          S.Yield x sa' -> return $ S.Yield x (SAL sa')
                          S.Skip    sa' -> return $ S.Skip    (SAL sa')
                          S.Done        -> return $ S.Skip    (SAR tb)
    step (SAR   sb) = do
                        r <- stepb sb
                        case r of
                          S.Yield x sb' -> return $ S.Yield x (SAR sb')
                          S.Skip    sb' -> return $ S.Skip    (SAR sb')
                          S.Done        -> return $ S.Done


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

