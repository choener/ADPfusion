
{-# Language MagicHash #-}

module ADP.Fusion.Core.Multi where

import qualified Data.Vector.Fusion.Stream.Monadic as S
import           Data.Vector.Fusion.Stream.Monadic
import           Data.Strict.Tuple
import           Data.Proxy
import           Prelude hiding (map)
import           GHC.Exts
import           Debug.Trace

import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Core.Classes
import           ADP.Fusion.Core.TyLvlIx



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
type instance TermArg (TermSymbol a b) = TermArg a :. TermArg b

instance (Element ls i) => Element (ls :!: TermSymbol a b) i where
  data Elm (ls :!: TermSymbol a b) i = ElmTS !(TermArg (TermSymbol a b)) !(RunningIndex i) !(Elm ls i)
  type Arg (ls :!: TermSymbol a b)   = Arg ls :. TermArg (TermSymbol a b)
  getArg (ElmTS a _ ls) = getArg ls :. a
  getIdx (ElmTS _ i _ ) = i
  {-# INLINE getArg #-}
  {-# INLINE getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (TermArg (TermSymbol a b)), Show (Elm ls i)) => Show (Elm (ls :!: TermSymbol a b) i)

instance
  ( Monad m
  , MkStream m ls i
  , Element ls i
  , TermStaticVar (TermSymbol a b) i
  , TermStream m (TermSymbol a b) (Elm ls i) i
  ) => MkStream m (ls :!: TermSymbol a b) i where
  mkStream grd (ls :!: ts) sv lu i
    = map (\(TState sS ii ee) -> ElmTS ee ii sS)
    . termStream ts sv lu i
    . map (\s -> TState s RiZ Z)
    $ mkStream (grd `andI#` termStaticCheck ts i) ls (termStaticVar ts sv i) lu (termStreamIndex ts sv i)
  {-# Inline mkStream #-}

instance Monad m => MkStream m S Z where
  mkStream grd S Z Z Z = S.filter (const $ isTrue# grd) $ S.singleton $ ElmS RiZ
  {-# INLINE mkStream #-}

-- | For multi-dimensional terminals we need to be able to calculate how the
-- static/variable signal changes and if the index for the inner part needs to
-- be modified.

class TermStaticVar t i where
  termStaticVar   :: t -> Context i -> i -> Context i
  termStreamIndex :: t -> Context i -> i -> i
  termStaticCheck ∷ t → i → Int#

instance TermStaticVar M Z where
  termStaticVar   _ _ _ = Z
  termStreamIndex _ _ _ = Z
  termStaticCheck _ _ = 1#
  {-# INLINE [0] termStaticVar #-}
  {-# INLINE [0] termStreamIndex #-}
  {-# INLINE [0] termStaticCheck #-}

instance
  ( TermStaticVar a is
  , TermStaticVar b i
  ) => TermStaticVar (TermSymbol a b) (is:.i) where
  termStaticVar   (a:|b) (vs:.v) (is:.i) = termStaticVar   a vs is :. termStaticVar   b v i
  termStreamIndex (a:|b) (vs:.v) (is:.i) = termStreamIndex a vs is :. termStreamIndex b v i
  termStaticCheck (a:|b) (is:.i) = termStaticCheck a is `andI#` termStaticCheck b i
  {-# INLINE [0] termStaticVar #-}
  {-# INLINE [0] termStreamIndex #-}
  {-# INLINE [0] termStaticCheck #-}

instance RuleContext Z where
  type Context Z = Z
  initialContext _ = Z
  {-# INLINE initialContext #-}

instance (RuleContext is, RuleContext i) => RuleContext (is:.i) where
  type Context (is:.i) = Context is:.Context i
  initialContext (is:.i) = initialContext is:.initialContext i
  {-# INLINE initialContext #-}

class TableStaticVar u c i where
  tableStaticVar   :: Proxy u -> c -> Context i -> i -> Context i
  tableStreamIndex :: Proxy u -> c -> Context i -> i -> i

instance TableStaticVar c u Z where
  tableStaticVar   _ _ _ _ = Z
  tableStreamIndex _ _ _ _ = Z
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance (TableStaticVar us cs is, TableStaticVar u c i) => TableStaticVar (us:.u) (cs:.c) (is:.i) where
  tableStaticVar   _ (cs:.c) (vs:.v) (is:.i) = tableStaticVar   (Proxy :: Proxy us) cs vs is :. tableStaticVar   (Proxy :: Proxy u) c v i
  tableStreamIndex _ (cs:.c) (vs:.v) (is:.i) = tableStreamIndex (Proxy :: Proxy us) cs vs is :. tableStreamIndex (Proxy :: Proxy u) c v i
  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}



data TermState s i e = TState
  { tS  :: !s
    -- ^ state coming in from the left
  , iIx :: !(RunningIndex i)
    -- ^ @I/C@ building up state to hand over to next symbol
  , eTS :: !e
    -- ^ element data
  }

class TermStream m t s i where
  termStream :: t -> Context i -> i -> i -> Stream m (TermState s Z Z) -> Stream m (TermState s i (TermArg t))

instance (Monad m) => TermStream m M s Z where
  termStream _ _ _ _ = id -- map (\(!s) -> s)
  {-# Inline termStream #-}

-- |
--
-- TODO need @t -> ElmType t@ type function
--
-- TODO need to actually return an @ElmType t@ can do that instead of
-- returning @u@ !!!

addTermStream1
  :: ( Monad m
     , TermStream m (TermSymbol M t) (Elm (Term1 s) (Z:.i)) (Z:.i)
     )
  => t -> Context i -> i -> i -> Stream m s -> Stream m (s,TermArg t,RunningIndex i)
addTermStream1 t c u i
  = map (\(TState (ElmTerm1 sS) (RiZ:.:ii) (Z:.ee)) -> (sS,ee,ii))
  . termStream (M:|t) (Z:.c) (Z:.u) (Z:.i)
  . map (\s -> TState (elmTerm1 s i) RiZ Z)
{-# Inline addTermStream1 #-}

newtype Term1 s = Term1 s

elmTerm1 :: s -> i -> Elm (Term1 s) (Z:.i)
elmTerm1 s _ = ElmTerm1 s
{-# Inline elmTerm1 #-}

instance (s ~ Elm x0 i, Element x0 i) => Element (Term1 s) (Z:.i) where
  newtype Elm (Term1 s) (Z:.i) = ElmTerm1 s
  getIdx (ElmTerm1 s) = RiZ :.: getIdx s
  {-# Inline getIdx #-}

-- | @Term MkStream@ context

type TmkCtx1 m ls t i
  = ( Monad m
    , MkStream m ls i
    , TermStream m (TermSymbol M t) (Elm (Term1 (Elm ls i)) (Z:.i)) (Z:.i)
    , Element ls i
    , TermStaticVar t i
    )

-- | @Term TermStream@ context

type TstCtx m ts s x0 sixty is i
  = ( Monad m
    , TermStream m ts s is
    , GetIndex (RunningIndex sixty) (RunningIndex (is:.i))
    , GetIx (RunningIndex sixty) (RunningIndex (is:.i)) ~ (RunningIndex i)
    , Element x0 sixty
    , s ~ Elm x0 sixty
    )

-- | Shorthand for proxifying @getIndex@

type PRI is i = Proxy (RunningIndex (is:.i))

