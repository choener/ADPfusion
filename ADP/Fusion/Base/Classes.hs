
{-# Language DefaultSignatures #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language StandaloneDeriving #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}

module ADP.Fusion.Base.Classes where

import           Data.Strict.Tuple
import           Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Fusion.Stream.Monadic as S

import           Data.PrimitiveArray



data OutsideContext s
  = OStatic     s
  | ORightOf    s
  | OFirstLeft  s
  | OLeftOf     s

data InsideContext
  = IStatic
  | IVariable

data ComplementContext
  = Complemented

class RuleContext i where
  type Context i :: *
  initialContext :: i -> Context i

-- | During construction of the stream, we need to extract individual elements
-- from symbols in production rules. An element in a stream is fixed by both,
-- the type @x@ of the actual argument we want to grab (say individual
-- characters we parse from an input) and the type of indices @i@ we use.
--
-- @Elm@ data constructors are all eradicated during fusion and should never
-- show up in CORE.

class Element x i where
  data Elm x i :: *
  type Arg x :: *
  getArg :: Elm x i -> Arg x
  getIdx :: Elm x i -> i
  getOmx :: Elm x i -> i

-- | @mkStream@ creates the actual stream of elements (@Elm@) that will be fed
-- to functions on the left of the @(<<<)@ operator. Streams work over all
-- monads and are specialized for each combination of arguments @x@ and indices
-- @i@.

class (Monad m) => MkStream m x i where
  mkStream :: x -> Context i -> i -> i -> S.Stream m (Elm x i)

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
  data Elm S i = ElmS !i !i
  type Arg S   = Z
  getArg (ElmS _ _) = Z
  getIdx (ElmS i _) = i
  getOmx (ElmS _ o) = o
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}

deriving instance Show ix => Show (Elm S ix)

-- | 'staticCheck' acts as a static filter. If 'b' is true, we keep all stream
-- elements. If 'b' is false, we discard all stream elements.

staticCheck :: Monad m => Bool -> S.Stream m a -> S.Stream m a
staticCheck b (S.Stream step t n) = b `seq` S.Stream snew (CheckLeft (b:.t)) (toMax n) where
  {-# Inline [0] snew #-}
  snew (CheckLeft  (False:._)) = return $ S.Done
  snew (CheckLeft  (True :.s)) = return $ S.Skip (CheckRight s)
  snew (CheckRight s         ) = do r <- step s
                                    case r of
                                      S.Yield x s' -> return $ S.Yield x (CheckRight s')
                                      S.Skip    s' -> return $ S.Skip    (CheckRight s')
                                      S.Done       -> return $ S.Done
{-# INLINE staticCheck #-}

data StaticCheck a b = CheckLeft a | CheckRight b


-- | Constrains the behaviour of the memoizing tables. They may be 'EmptyOk' if
-- @i==j@ is allowed (empty subwords or similar); or they may need 'NonEmpty'
-- indices, or finally they can be 'OnlyZero' (only @i==j@ allowed) which is
-- useful in multi-dimensional casese.

data TableConstraint
  = EmptyOk
  | NonEmpty
  | OnlyZero
  deriving (Eq,Show)

minSize :: TableConstraint -> Int
minSize NonEmpty = 1
minSize _        = 0
{-# INLINE minSize #-}

class ModifyConstraint t where
  toNonEmpty :: t -> t
  toEmpty    :: t -> t

-- |

type family   TblConstraint x       :: *

type instance TblConstraint (is:.i)        =  TblConstraint is :. TblConstraint i
type instance TblConstraint Z              = Z
type instance TblConstraint (Outside o)    = TblConstraint o
type instance TblConstraint (Complement o) = TblConstraint o

type instance TblConstraint PointL      = TableConstraint
type instance TblConstraint PointR      = TableConstraint
type instance TblConstraint Subword     = TableConstraint

