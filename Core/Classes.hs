
{-# Language MagicHash, UnboxedTuples #-}

module ADPfusion.Core.Classes where

import           Control.DeepSeq
import           Data.Proxy
import           Data.Strict.Tuple
import           GHC.Exts hiding (build)
import           GHC.Generics (Generic, Generic1)
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray.Index.Class



-- TODO Until I figure out how to use @InitialContext ∷ k@ instead of
-- @InitialContext ∷ *@ we need to live in @*@. Unfortunately, @(<<<)@ does not
-- like differently-kinded types.

{-
data OutsideContext s
  = OStatic     s
  | ORightOf    s
  | OFirstLeft  s
  | OLeftOf     s
  deriving (Show)
-}
data OStatic    s
data ORightOf   s
data OFirstLeft s
data OLeftOf    s

{-
data InsideContext s
  = IStatic   {iGetContext :: s}
  | IVariable {iGetContext :: s}
  deriving (Show)
-}
data IStatic   s
data IVariable s

{-
data ComplementContext
  = Complemented
  deriving (Show)
-}
data Complement

-- | Needed for structures that have long-range interactions and "expand",
-- like sets around edge boundaries: @set <edge> set@. requires the sets to
-- be connected.

data ExtComplementContext s
  = CStatic s
  | CVariable s

-- | For each index type @ix@, @initialContext (Proxy ∷ ix)@ yields the initial
-- context from which to start up rules.
--
-- TODO turn into type family and make 'initialContext' a global function.

type family InitialContext ix ∷ *

{-
class RuleContext ix where
  type InitialContext ix ∷ *
  initialContext ∷ Proxy ix → Proxy (InitialContext ix)
--  default initialContext ∷ Proxy ix → Proxy (InitialContext ix ∷ k)
  initialContext Proxy = Proxy
  {-# Inline initialContext #-}
-}

-- | While we ostensibly use an index of type @i@ we typically do not need
-- every element of an @i@. For example, when looking at 'Subword's, we do
-- not need both element of @j:.k@ but only @k@.
-- Also, inside grammars do need fewer moving indices than outside
-- grammars.

data family RunningIndex i :: *

data instance RunningIndex Z = RiZ
  deriving (Generic, NFData, Show)

data instance RunningIndex (is:.i) = !(RunningIndex is) :.: !(RunningIndex i)
  deriving (Generic)

deriving instance (NFData (RunningIndex is), NFData (RunningIndex i)) => NFData (RunningIndex (is:.i))

-- | During construction of the stream, we need to extract individual elements
-- from symbols in production rules. An element in a stream is fixed by both,
-- the type @x@ of the actual argument we want to grab (say individual
-- characters we parse from an input) and the type of indices @i@ we use.
--
-- @Elm@ data constructors are all eradicated during fusion and should never
-- show up in CORE.

class Element (x ∷ *) i where
  -- | Runtime representation of parsed elements "in flight". A parser of @x@s with index @i@
  -- creates a stream of @Elm x i@s with the goal that the @Elm@ representation will be fused away.
  -- Each @Elm@ will hold parsed elements, say @c@ given a list @[c]@. It will also hold
  -- @RunningIndex@ indices, and finally a recursive way to attach more symbols (by attaching
  -- another @Elm@ inside.
  data Elm    x i ∷ *
  -- | Provide access to the recursive @Elm@ stack. This allows inspection of all previous elements.
  -- Used by "split symbols" that need to access prior indices.
  type RecElm x i ∷ *
  -- | The argument of the parser is a single parsed type for the collection type @x@. Say @c@ given
  -- @[c]@.
  type Arg    x   ∷ *
  -- | Extract the argument from an elm. Used by parser implementations.
  getArg ∷ Elm x i → Arg x
  -- | Extract the running index.
  getIdx ∷ Elm x i → RunningIndex i
  -- | Extract the full re
  getElm ∷ Elm x i → RecElm x i

-- | @mkStream@ creates the actual stream of elements (@Elm@) that will be fed
-- to functions on the left of the @(<<<)@ operator. Streams work over all
-- monads and are specialized for each combination of arguments @x@ and indices
-- @i@.

class (Monad m) ⇒ MkStream m pos sym ix where
  mkStream
    ∷ Proxy pos
    -- ^ Fix static/variable/... depending on position in r.h.s. of rule.
    → sym
    -- ^ the symbol type (syntactic variable with or with memoization, terminal types like char, string, etc)
    → Int#
    -- ^ guard system for stopping execution of rule
    → LimitType ix
    -- ^ upper limit of index @i@, using the specialized 'LimitType' for type @i@.
    → ix
    -- ^ the current index @i@
    → S.Stream m (Elm sym ix)
    -- ^ resulting stream of elements

-- | This type family yields for a given positional type @posty ∷ k@, the
-- current symbol type @symty@ and index type @ix@ the next-left positional
-- type within the same kind @k@ Keeping within the same kind should prevent
-- accidental switching from Inside to Outside or similar bugs.

type family LeftPosTy (pos ∷ *) sym ix ∷ *

-- | Finally, we need to be able to correctly build together symbols on the
-- right-hand side of the @(<<<)@ operator.
--
-- The default makes sure that the last (or only) argument left over is
-- correctly assigned a @Z@ to terminate the symbol stack.

class Build x where
  type Stack x :: *
  type Stack x = S :!: x
  build :: x -> Stack x
  default build :: (Stack x ~ (S :!: x)) => x -> Stack x
  build x = S :!: x
  {-# Inline build #-}

instance Build x => Build (x:!:y) where
  type Stack (x:!:y) = Stack x :!: y
  build (x:!:y) = build x :!: y
  {-# Inline build #-}

-- | Similar to 'Z', but terminates an argument stack.

data S = S
  deriving (Eq,Show)

instance
  (
  ) => Element S i where
  newtype Elm S i = ElmS (RunningIndex i)
  type Arg S   = Z
  type RecElm S i = Z
  getArg (ElmS _) = Z
  getIdx (ElmS i) = i
  getElm (ElmS _) = Z
  {-# Inline [0] getArg #-}
  {-# Inline [0] getIdx #-}
  {-# Inline [0] getElm #-}

deriving instance (Show (RunningIndex ix)) => Show (Elm S ix)

-- | 'staticCheck' acts as a static filter. If 'b' is true, we keep all stream
-- elements. If 'b' is false, we discard all stream elements.

staticCheck :: Monad m => Bool -> S.Stream m a -> S.Stream m a
staticCheck !b (S.Stream step t) = S.Stream snew (CheckLeft b t) where
  {-# Inline [0] snew #-}
  snew (CheckLeft  False _) = return $ S.Done
  snew (CheckLeft  True  s) = return $ S.Skip (CheckRight s)
  snew (CheckRight s      ) = do r <- step s
                                 case r of
                                   S.Yield x s' -> return $ S.Yield x (CheckRight s')
                                   S.Skip    s' -> return $ S.Skip    (CheckRight s')
                                   S.Done       -> return $ S.Done
{-# INLINE staticCheck #-}

data StaticCheck a b = CheckLeft Bool a | CheckRight b

staticCheck# :: Monad m => Int# -> S.Stream m a -> S.Stream m a
staticCheck# b (S.Stream step t) = S.Stream snew (SL b t) where
  {-# Inline [0] snew #-}
  snew (SL q s)
    | 1# <- q   = return $ S.Skip (SR s)
    | otherwise = return $ S.Done
  snew (SR s  ) = do r <- step s
                     case r of
                       S.Yield x s' -> return $ S.Yield x (SR s')
                       S.Skip    s' -> return $ S.Skip    (SR s')
                       S.Done       -> return $ S.Done
{-# Inline staticCheck# #-}


data SLR z = SL Int# z | SR z

-- | Constrains the behaviour of the memoizing tables. They may be 'EmptyOk' if
-- @i==j@ is allowed (empty subwords or similar); or they may need 'NonEmpty'
-- indices, or finally they can be 'OnlyZero' (only @i==j@ allowed) which is
-- useful in multi-dimensional casese.

data EmptyOk = EmptyOk
  deriving (Show)

data NonEmpty = NonEmpty
  deriving (Show)

class MinSize c where
  minSize :: c -> Int

instance MinSize EmptyOk where
  minSize EmptyOk = 0
  {-# Inline minSize #-}

instance MinSize NonEmpty where
  minSize NonEmpty = 1
  {-# Inline minSize #-}

-- |
--
-- TODO Rewrite to generalize easily over multi-dim cases.

class ModifyConstraint t where
  type TNE t :: *
  type TE  t :: *
  toNonEmpty :: t -> TNE t
  toEmpty    :: t -> TE  t

