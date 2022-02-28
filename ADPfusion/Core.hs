
{-# Language MagicHash #-}

-- | Generalized fusion system for grammars.
--
-- This module re-exports only the core functionality.
--
-- NOTE Symbols typically do not check bound data for consistency. If you, say,
-- bind a terminal symbol to an input of length 0 and then run your grammar,
-- you probably get errors, garbled data or random crashes. Such checks are
-- done via asserts in non-production code.

module ADPfusion.Core
  ( module ADPfusion.Core
  , module ADPfusion.Core.Apply
  , module ADPfusion.Core.Classes
  , module ADPfusion.Core.Multi
  , module ADPfusion.Core.SynVar.Array
  , module ADPfusion.Core.SynVar.Axiom
  , module ADPfusion.Core.SynVar.Backtrack
  , module ADPfusion.Core.SynVar.FillTyLvl
  , module ADPfusion.Core.SynVar.Indices
  , module ADPfusion.Core.SynVar.Recursive.Type
  , module ADPfusion.Core.SynVar.Split
  , module ADPfusion.Core.SynVar.TableWrap
  , module ADPfusion.Core.Term.Chr
  , module ADPfusion.Core.Term.Deletion
  , module ADPfusion.Core.Term.Edge
  , module ADPfusion.Core.Term.Epsilon
  , module ADPfusion.Core.Term.MultiChr
  , module ADPfusion.Core.Term.PeekIndex
  , module ADPfusion.Core.Term.Str
  , module ADPfusion.Core.Term.Switch
  , module ADPfusion.Core.TH
  , module ADPfusion.Core.TyLvlIx
  , module Data.Vector.Fusion.Stream.Monadic
  , module Data.Vector.Fusion.Util
  ) where

import           Data.Vector.Fusion.Stream.Monadic (Stream (..))
import           Data.Strict.Tuple
import           GHC.Exts (inline)
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           Data.Vector.Fusion.Util (Id(..))

import           Data.PrimitiveArray

import           ADPfusion.Core.Apply
import           ADPfusion.Core.Classes hiding (iIx)
import           ADPfusion.Core.Multi hiding (iIx)
import           ADPfusion.Core.SynVar.Array
import           ADPfusion.Core.SynVar.Axiom
import           ADPfusion.Core.SynVar.Backtrack
import           ADPfusion.Core.SynVar.FillTyLvl
import           ADPfusion.Core.SynVar.Indices
import           ADPfusion.Core.SynVar.Recursive.Type
import           ADPfusion.Core.SynVar.Split
import           ADPfusion.Core.SynVar.TableWrap
import           ADPfusion.Core.Term.Chr
import           ADPfusion.Core.Term.Deletion
import           ADPfusion.Core.Term.Edge
import           ADPfusion.Core.Term.Epsilon
import           ADPfusion.Core.Term.MultiChr
import           ADPfusion.Core.Term.PeekIndex
import           ADPfusion.Core.Term.Str
import           ADPfusion.Core.Term.Switch
import           ADPfusion.Core.TH
import           ADPfusion.Core.TyLvlIx

-- we do not want since those explicit @f = \ij@ are to keep the fusion system happy
-- TODO might have changed with newer GHC and should be checked
{-# ANN module ("HLint: ignore Redundant lambda" :: String) #-}



-- | Apply a function to symbols on the RHS of a production rule. Builds the
-- stack of symbols from 'xs' using 'build', then hands this stack to
-- 'mkStream' together with the initial 'iniT' telling 'mkStream' that we are
-- in the "outer" position. Once the stream has been created, we 'S.map'
-- 'getArg' to get just the arguments in the stack, and finally 'apply' the
-- function 'f'.

infixl 8 <<<
(<<<)
  :: forall k m initCtx symbols i b
  . ( Monad m
    , Build symbols
    , Element (Stack symbols) i
    , Apply (Arg (Stack symbols) → b)
    , initCtx ~ InitialContext i
    , MkStream m initCtx (Stack symbols) i
    )
  => (Fun (Arg (Stack symbols) → b))
  -> symbols
  -> (LimitType i → i → Stream m b)
(<<<) f xs
  = \lu ij
  -> S.map (apply (inline f) . getArg)
  $ mkStream (Proxy :: Proxy initCtx) (build xs) 1# lu ij
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
(...) s h = \lu ij -> h $ s lu ij
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

