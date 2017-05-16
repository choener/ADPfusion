
{-# Language MagicHash #-}

module ADP.Fusion.Core.Classes where

import           Data.Proxy
import           Data.Strict.Tuple
import           GHC.Exts hiding (build)
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray



data OutsideContext s
  = OStatic     s
  | ORightOf    s
  | OFirstLeft  s
  | OLeftOf     s
  deriving (Show)

data InsideContext s
  = IStatic   {iGetContext :: s}
  | IVariable {iGetContext :: s}
  deriving (Show)

data ComplementContext
  = Complemented
  deriving (Show)

-- | Needed for structures that have long-range interactions and "expand",
-- like sets around edge boundaries: @set <edge> set@. requires the sets to
-- be connected.

data ExtComplementContext s
  = CStatic s
  | CVariable s

class RuleContext i where
  type Context i :: *
  initialContext :: i -> Context i

-- | While we ostensibly use an index of type @i@ we typically do not need
-- every element of an @i@. For example, when looking at 'Subword's, we do
-- not need both element of @j:.k@ but only @k@.
-- Also, inside grammars do need fewer moving indices than outside
-- grammars.
--
-- TODO Sometimes, the actual RunningIndex ctors are not erased. This could
-- be due to <https://ghc.haskell.org/trac/ghc/ticket/2289>. To test, we
-- should transform RunningIndex into a type class to give us access to the
-- left and right member, also we should create instances a la
-- @RunningIndex (is :. Subword I) = RiSwI !(RunningIndex is) !Int@.
-- Hopefully, these are completely erased.

{-
class RunningIndexCl i where
  type RecursiveRl i :: *
  type ThisRI i :: *
-}

data family RunningIndex i :: *

data instance RunningIndex (is:.i) = !(RunningIndex is) :.: !(RunningIndex i)

data instance RunningIndex Z = RiZ

deriving instance Show (RunningIndex Z)


-- | During construction of the stream, we need to extract individual elements
-- from symbols in production rules. An element in a stream is fixed by both,
-- the type @x@ of the actual argument we want to grab (say individual
-- characters we parse from an input) and the type of indices @i@ we use.
--
-- @Elm@ data constructors are all eradicated during fusion and should never
-- show up in CORE.

class Element x i where
  data Elm    x i :: *
  type RecElm x i :: *
  type Arg    x   :: *
  getArg :: Elm x i -> Arg x
  getIdx :: Elm x i -> RunningIndex i
  getElm :: Elm x i -> RecElm x i

-- | @mkStream@ creates the actual stream of elements (@Elm@) that will be fed
-- to functions on the left of the @(<<<)@ operator. Streams work over all
-- monads and are specialized for each combination of arguments @x@ and indices
-- @i@.

class (Monad m) => MkStream m x i where
  mkStream :: Int# -> x -> Context i -> i -> i -> S.Stream m (Elm x i)

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
  data Elm S i = ElmS !(RunningIndex i)
  type Arg S   = Z
  getArg (ElmS _) = Z
  getIdx (ElmS i) = i
  {-# Inline getArg #-}
  {-# Inline getIdx #-}

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
staticCheck# !b (S.Stream step t) = S.Stream snew (SL t b) where
  {-# Inline [0] snew #-}
  snew (SL s k)
    | 1# <- k   = return $ S.Skip (SR s)
    | otherwise = return $ S.Done
  snew (SR s  ) = do r <- step s
                     case r of
                       S.Yield x s' -> return $ S.Yield x (SR s')
                       S.Skip    s' -> return $ S.Skip    (SR s')
                       S.Done       -> return $ S.Done
{-# Inline staticCheck# #-}


data SLR z = SL z Int# | SR z

-- | Constrains the behaviour of the memoizing tables. They may be 'EmptyOk' if
-- @i==j@ is allowed (empty subwords or similar); or they may need 'NonEmpty'
-- indices, or finally they can be 'OnlyZero' (only @i==j@ allowed) which is
-- useful in multi-dimensional casese.

--data TableConstraint
--  = EmptyOk
--  | NonEmpty
--  | OnlyZero
--  deriving (Eq,Show)

data EmptyOk = EmptyOk

data NonEmpty = NonEmpty

class MinSize c where
  minSize :: c -> Int

instance MinSize EmptyOk where
  minSize EmptyOk = 0
  {-# Inline minSize #-}

instance MinSize NonEmpty where
  minSize NonEmpty = 1
  {-# Inline minSize #-}

{-
minSize :: TableConstraint -> Int
minSize NonEmpty = 1
minSize _        = 0
{-# Inline [0] minSize #-}
-}

-- |
--
-- TODO Rewrite to generalize easily over multi-dim cases.

class ModifyConstraint t where
  type TNE t :: *
  type TE  t :: *
  toNonEmpty :: t -> TNE t
  toEmpty    :: t -> TE  t

--
--instance ModifyConstraint EmptyOk
--  type TNE EmptyOk = NonEmpty
--  type TE  EmptyOk = 

-- |

--type family   TblConstraint x       :: *
--
--type instance TblConstraint (is:.i) =  TblConstraint is :. TblConstraint i
--type instance TblConstraint Z       = Z
--
---- TODO move into the sub-modules
--
--type instance TblConstraint (PointL  t) = TableConstraint
--type instance TblConstraint (PointR  t) = TableConstraint
--type instance TblConstraint (Subword t) = TableConstraint

