
module ADP.Fusion.Base.Multi where

import qualified Data.Vector.Fusion.Stream.Monadic as S
import           Data.Strict.Tuple
import           Data.Proxy

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

data TermState s a u i e = TState
  { sS  :: !s -- | state coming in from the left
  , sIx :: !a -- | @I/C@ index from @sS@
  , sOx :: !a -- | @O@ index from @sS@
  , tIx :: !u -- | @I/C@ building up state to index the @table@.
  , tOx :: !u -- | @O@ building up state to index the @table@ (for @O tables@).
  , iIx :: !i -- | @I/C@ building up state to hand over to next symbol
  , iOx :: !i -- | @O@ building up state to hand over to next symbol
  , eTS :: !e -- | element data
  }

class TermStream m t u i where
  termStream :: t -> i -> i -> S.Stream m (TermState s a Z Z Z) -> S.Stream m (TermState s a u i (TermArg t))

instance TermStream m M Z Z where
  termStream _ _ _ = id
  {-# Inline termStream #-}

-- | Handles each individual argument within a stack of terminal symbols.

class TerminalStream m t i where
  terminalStream :: t -> Context i -> i -> S.Stream m (S5 s j j i i) -> S.Stream m (S6 s j j i i (TermArg t))

iPackTerminalStream a sv    (ii:._)  = terminalStream a sv ii     . S.map (\(S5 s zi zo    (is:.i)     (os:.o) ) -> S5 s (zi:.i) (zo:.o)    is     os )
{-# Inline iPackTerminalStream #-}

instance (Monad m) => TerminalStream m M Z where
  terminalStream M _ Z = S.map (\(S5 s j1 j2 Z Z) -> S6 s j1 j2 Z Z Z)
  {-# INLINE terminalStream #-}

instance Monad m => MkStream m S Z where
  mkStream _ _ _ _ = S.singleton (ElmS Z Z)
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

instance
  ( TermStaticVar a is
  , TermStaticVar b i
  ) => TermStaticVar (TermSymbol a b) (is:.i) where
  termStaticVar   (a:|b) (vs:.v) (is:.i) = termStaticVar   a vs is :. termStaticVar   b v i
  termStreamIndex (a:|b) (vs:.v) (is:.i) = termStreamIndex a vs is :. termStreamIndex b v i
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

instance (RuleContext is, RuleContext i) => RuleContext (is:.i) where
  type Context (is:.i) = Context is:.Context i
  initialContext (is:.i) = initialContext is:.initialContext i
  {-# INLINE initialContext #-}

class TableStaticVar u i where
  tableStaticVar   :: Proxy u -> TblConstraint u -> Context i -> i -> Context i
  tableStreamIndex :: Proxy u -> TblConstraint u -> Context i -> i -> i

instance TableStaticVar u Z where
  tableStaticVar   _ _ _ _ = Z
  tableStreamIndex _ _ _ _ = Z
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance (TableStaticVar us is, TableStaticVar u i) => TableStaticVar (us:.u) (is:.i) where
  tableStaticVar   _ (cs:.c) (vs:.v) (is:.i) = tableStaticVar   (Proxy :: Proxy us) cs vs is :. tableStaticVar   (Proxy :: Proxy u) c v i
  tableStreamIndex _ (cs:.c) (vs:.v) (is:.i) = tableStreamIndex (Proxy :: Proxy us) cs vs is :. tableStreamIndex (Proxy :: Proxy u) c v i
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

