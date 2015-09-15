
module ADP.Fusion.Base.Multi where

import qualified Data.Vector.Fusion.Stream.Monadic as S
import           Data.Strict.Tuple

import           Data.PrimitiveArray

import           ADP.Fusion.Base.Classes



-- * Multi-dimensional extension

-- | Terminates a multi-dimensional terminal symbol stack.

data M = M
  deriving (Eq,Show)

infixl 2 :|

-- | Terminal symbols are stacked together with @a@ tails and @b@ head.

data TermSymbol a b = a :| b
  deriving (Eq,Show)

instance Build (TermSymbol a b)

-- | Extracts the type of a multi-dimensional terminal argument.

type family   TermArg x :: *
type instance TermArg M                = Z

instance (Element ls i) => Element (ls :!: TermSymbol a b) i where
  data Elm (ls :!: TermSymbol a b) i = ElmTS !(TermArg (TermSymbol a b)) !i !i !(Elm ls i)
  type Arg (ls :!: TermSymbol a b)   = Arg ls :. TermArg (TermSymbol a b)
  getArg (ElmTS a _ _ ls) = getArg ls :. a
  getIdx (ElmTS _ i _ _ ) = i
  getOmx (ElmTS _ _ o _ ) = o
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

deriving instance (Show i, Show (TermArg (TermSymbol a b)), Show (Elm ls i)) => Show (Elm (ls :!: TermSymbol a b) i)

instance
  ( Monad m
  , MkStream m ls i
  , Element ls i
  , TerminalStream m (TermSymbol a b) i
  , TermStaticVar (TermSymbol a b) i
  ) => MkStream m (ls :!: TermSymbol a b) i where
  mkStream (ls :!: ts) sv lu i
    = S.map fromTerminalStream
    . terminalStream ts sv i
    . S.map toTerminalStream
    $ mkStream ls (termStaticVar ts sv i) lu (termStreamIndex ts sv i)
  {-# Inline mkStream #-}

-- | Handles each individual argument within a stack of terminal symbols.

class TerminalStream m t i where
  terminalStream :: t -> Context i -> i -> S.Stream m (S5 s j j i i) -> S.Stream m (S6 s j j i i (TermArg t))

iPackTerminalStream a sv    (ii:._)  = terminalStream a sv ii     . S.map (\(S5 s zi zo    (is:.i)     (os:.o) ) -> S5 s (zi:.i) (zo:.o)    is     os )
{-# Inline iPackTerminalStream #-}

oPackTerminalStream a sv (O (is:.i)) = terminalStream a sv (O is) . S.map (\(S5 s zi zo (O (is:.i)) (O (os:.o))) -> S5 s (zi:.i) (zo:.o) (O is) (O os))
{-# Inline oPackTerminalStream #-}

instance (Monad m) => TerminalStream m M Z where
  terminalStream M _ Z = S.map (\(S5 s j1 j2 Z Z) -> S6 s j1 j2 Z Z Z)
  {-# INLINE terminalStream #-}

instance (Monad m) => TerminalStream m M (Outside Z) where
  terminalStream M _ (O Z) = S.map (\(S5 s j1 j2 (O Z) (O Z)) -> S6 s j1 j2 (O Z) (O Z) Z)
  {-# INLINE terminalStream #-}

instance Monad m => MkStream m S Z where
  mkStream _ _ _ _ = S.singleton (ElmS Z Z)
  {-# INLINE mkStream #-}

instance Monad m => MkStream m S (Outside Z) where
  mkStream _ _ _ _ = S.singleton (ElmS (O Z) (O Z))
  {-# INLINE mkStream #-}

-- | For multi-dimensional terminals we need to be able to calculate how the
-- static/variable signal changes and if the index for the inner part needs to
-- be modified.

class TermStaticVar t i where
  termStaticVar   :: t -> Context i -> i -> Context i
  termStreamIndex :: t -> Context i -> i -> i

instance TermStaticVar M Z where
  termStaticVar   _ _ _ = Z
  termStreamIndex _ _ _ = Z
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

instance TermStaticVar M (Outside Z) where
  termStaticVar   _ _ _ = Z
  termStreamIndex _ _ _ = O Z
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

instance
  ( TermStaticVar a is
  , TermStaticVar b i
  ) => TermStaticVar (TermSymbol a b) (is:.i) where
  termStaticVar   (a:|b) (vs:.v) (is:.i) = termStaticVar   a vs is :. termStaticVar   b v i
  termStreamIndex (a:|b) (vs:.v) (is:.i) = termStreamIndex a vs is :. termStreamIndex b v i
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

instance
  ( TermStaticVar a (Outside is)
  , TermStaticVar b (Outside i)
  ) => TermStaticVar (TermSymbol a b) (Outside (is:.i)) where
  termStaticVar   (a:|b) (vs:.v) (O (is:.i)) = termStaticVar   a vs (O is) :. termStaticVar   b v (O i)
  termStreamIndex (a:|b) (vs:.v) (O (is:.i)) =
    let (O js) = termStreamIndex a vs (O is)
        (O j)  = termStreamIndex b v (O i)
    in O (js:.j)
  {-# INLINE termStaticVar #-}
  {-# INLINE termStreamIndex #-}

data S3 a b c           = S3 !a !b !c

data S4 a b c d         = S4 !a !b !c !d

data S5 a b c d e       = S5 !a !b !c !d !e

data S6 a b c d e f     = S6 !a !b !c !d !e !f

data S7 a b c d e f g   = S7 !a !b !c !d !e !f !g

data S8 a b c d e f g h = S8 !a !b !c !d !e !f !g !h

fromTerminalStream (S6 s Z Z i o e) = ElmTS e i o s
{-# INLINE fromTerminalStream #-}

toTerminalStream s = S5 s Z Z (getIdx s) (getOmx s)
{-# INLINE toTerminalStream #-}

instance RuleContext Z where
  type Context Z = Z
  initialContext _ = Z
  {-# INLINE initialContext #-}

instance RuleContext (Outside Z) where
  type Context (Outside Z) = Z
  initialContext _ = Z
  {-# INLINE initialContext #-}

instance (RuleContext is, RuleContext i) => RuleContext (is:.i) where
  type Context (is:.i) = Context is:.Context i
  initialContext (is:.i) = initialContext is:.initialContext i
  {-# INLINE initialContext #-}

instance (RuleContext (Outside is), RuleContext (Outside i)) => RuleContext (Outside (is:.i)) where
  type Context (Outside (is:.i)) = Context (Outside is):.Context (Outside i)
  initialContext (O (is:.i)) = initialContext (O is):.initialContext (O i)
  {-# INLINE initialContext #-}

class TableStaticVar i where
  tableStaticVar   :: TblConstraint i -> Context i -> i -> Context i
  tableStreamIndex :: TblConstraint i -> Context i -> i -> i

instance TableStaticVar Z where
  tableStaticVar   _ _ _ = Z
  tableStreamIndex _ _ _ = Z
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance TableStaticVar (Outside Z) where
  tableStaticVar   _ _ _ = Z
  tableStreamIndex _ _ _ = O Z
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance (TableStaticVar is, TableStaticVar i) => TableStaticVar (is:.i) where
  tableStaticVar   (cs:.c) (vs:.v) (is:.i) = tableStaticVar   cs vs is :. tableStaticVar   c v i
  tableStreamIndex (cs:.c) (vs:.v) (is:.i) = tableStreamIndex cs vs is :. tableStreamIndex c v i
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance (TableStaticVar (Outside is), TableStaticVar (Outside i)) => TableStaticVar (Outside (is:.i)) where
  tableStaticVar   (cs:.c) (vs:.v) (O (is:.i)) = tableStaticVar cs vs (O is) :. tableStaticVar c v (O i)
  tableStreamIndex (cs:.c) (vs:.v) (O (is:.i)) =
    let (O js) = tableStreamIndex cs vs (O is)
        (O j)  = tableStreamIndex c  v  (O i)
    in O (js:.j)
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

