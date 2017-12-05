
{-# Language MagicHash #-}

module ADP.Fusion.Core.Multi where

import qualified Data.Vector.Fusion.Stream.Monadic as S
import           Data.Vector.Fusion.Stream.Monadic
import           Data.Strict.Tuple
import           Data.Proxy
import           Prelude hiding (map)
import           GHC.Exts
import           Debug.Trace

import           Data.PrimitiveArray.Index.Class hiding (map)

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
type instance TermArg (TermSymbol a b) = (TermArg a) :. (TermArg b)

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
  , MkStream m posLeft ls i
  , Element ls i
  , TermStaticVar pos (TermSymbol a b) i
  , TermStream m pos (TermSymbol a b) (Elm ls i) i
  , posLeft ~ LeftPosTy pos (ls :!: TermSymbol a b) i
  ) => MkStream m pos (ls :!: TermSymbol a b) i where
  mkStream p (ls :!: ts) grd lu i
    = map (\(TState sS ii ee) -> ElmTS ee ii sS)
    . termStream p ts lu i
    . map (\s -> TState s RiZ Z)
    $ mkStream (Proxy ∷ Proxy posLeft) ls (grd `andI#` termStaticCheck p ts i) lu (termStreamIndex p ts i)
  {-# Inline mkStream #-}

instance Monad m => MkStream m pos S Z where
  mkStream Proxy S grd ZZ Z = S.filter (const $ isTrue# grd) $ S.singleton $ ElmS RiZ
  {-# Inline mkStream #-}

-- | For multi-dimensional terminals we need to be able to calculate how the
-- static/variable signal changes and if the index for the inner part needs to
-- be modified.

class TermStaticVar pos sym ix where
--  termStaticVar   ∷ sym → Context i → i → Context i
  termStreamIndex ∷ Proxy pos → sym → ix → ix
  termStaticCheck ∷ Proxy pos → sym → ix → Int#

instance TermStaticVar pos M Z where
--  termStaticVar   _ _ _ = Z
  termStreamIndex Proxy M Z = Z
  termStaticCheck Proxy M Z = 1#
--  {-# INLINE [0] termStaticVar #-}
  {-# INLINE [0] termStreamIndex #-}
  {-# INLINE [0] termStaticCheck #-}

instance
  ( TermStaticVar ps ts is
  , TermStaticVar p  t  i
  ) => TermStaticVar (ps:.p) (TermSymbol ts t) (is:.i) where
--  termStaticVar   (a:|b) (vs:.v) (is:.i) = termStaticVar   a vs is :. termStaticVar   b v i
  termStreamIndex Proxy (ts:|t) (is:.i) = termStreamIndex (Proxy ∷ Proxy ps) ts is :. termStreamIndex (Proxy ∷ Proxy p) t i
  termStaticCheck Proxy (ts:|t) (is:.i) = termStaticCheck (Proxy ∷ Proxy ps) ts is `andI#` termStaticCheck (Proxy ∷ Proxy p) t i
--  {-# INLINE [0] termStaticVar #-}
  {-# INLINE [0] termStreamIndex #-}
  {-# INLINE [0] termStaticCheck #-}

instance RuleContext Z where
  type InitialContext Z = Z
  initialContext _ = Z
  {-# INLINE initialContext #-}

instance (RuleContext is, RuleContext i) => RuleContext (is:.i) where
  type InitialContext (is:.i) = InitialContext is:.InitialContext i
  initialContext Proxy = initialContext (Proxy ∷ Proxy is):.initialContext (Proxy ∷ Proxy i)
  {-# INLINE initialContext #-}

class TableStaticVar pos tableIx c ix where
  {- To be replaced by type function to calculate if we become variable ...
  tableStaticVar
    ∷ Proxy u
    → c
    → Context i
    → i
    → Context i
    -}
  tableStreamIndex
    ∷ Proxy pos
    -- ^ provide type-level information on if we are currently static/variable/
    -- etc
    → Proxy tableIx
    -- ^ provide type-level information on the index structure of the table we
    -- are looking at. This index structure might well be different than the
    -- @ix@ index we use in the grammar.
    → c
    -- ^ Information on the minimal size of the corresponding table.
    → ix
    -- ^ current upper bound on index
    → ix
    -- ^ next upper bound on index

instance TableStaticVar pos u c Z where
--  tableStaticVar   _ _ _ _ = Z
  tableStreamIndex _ _ _ _ = Z
--  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}

instance
  ( TableStaticVar ps us cs is
  , TableStaticVar p  u  c  i
  )
  ⇒ TableStaticVar ('(:.) ps p) (us:.u) (cs:.c) (is:.i) where
--  tableStaticVar   _ (cs:.c) (vs:.v) (is:.i) = tableStaticVar   (Proxy :: Proxy us) cs vs is :. tableStaticVar   (Proxy :: Proxy u) c v i
  tableStreamIndex Proxy Proxy (cs:.c) (is:.i) = tableStreamIndex (Proxy ∷ Proxy ps) (Proxy ∷ Proxy us) cs is :. tableStreamIndex (Proxy ∷ Proxy p) (Proxy ∷ Proxy u) c i
--  {-# INLINE [0] tableStaticVar   #-}
  {-# INLINE [0] tableStreamIndex #-}


data TermState s i e = TState
  { tS  :: !s
    -- ^ state coming in from the left
  , iIx :: !(RunningIndex i)
    -- ^ @I/C@ building up state to hand over to next symbol
  , eTS :: !e
    -- ^ element data
  }

class TermStream m pos t s i where
  termStream
    ∷ Proxy pos
    → t
    → LimitType i
    → i
    → Stream m (TermState s Z Z)
    → Stream m (TermState s i (TermArg t))

instance (Monad m) => TermStream m pos M s Z where
  termStream Proxy M ZZ Z = id
  {-# Inline termStream #-}

-- |
--
-- TODO need @t -> ElmType t@ type function
--
-- TODO need to actually return an @ElmType t@ can do that instead of
-- returning @u@ !!!

addTermStream1
  ∷ forall m pos t s i
  . ( Monad m
    , TermStream m ('(:.) Z pos) (TermSymbol M t) (Elm (Term1 s) (Z:.i)) (Z:.i)
    )
  ⇒ Proxy pos
  → t
  → LimitType i
  → i
  → Stream m s
  → Stream m (s,TermArg t,RunningIndex i)
addTermStream1 Proxy t u i
  = map (\(TState (ElmTerm1 sS) (RiZ:.:ii) (Z:.ee)) -> (sS,ee,ii))
  . termStream (Proxy ∷ Proxy ('(:.) Z pos)) (M:|t) (ZZ:..u) (Z:.i)
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

type TmkCtx1 m (pos ∷ k) ls t i
  = ( Monad m
    , MkStream m pos ls i
    , TermStream m pos (TermSymbol M t) (Elm (Term1 (Elm ls i)) (Z:.i)) (Z:.i)
    , Element ls i
    , TermStaticVar pos t i
    )

-- | @Term TermStream@ context

type TstCtx m (pos ∷ k) ts s x0 sixty is i
  = ( Monad m
    , TermStream m pos ts s is
    , GetIndex (RunningIndex sixty) (RunningIndex (is:.i))
    , GetIx (RunningIndex sixty) (RunningIndex (is:.i)) ~ (RunningIndex i)
    , Element x0 sixty
    , s ~ Elm x0 sixty
    )

-- | Shorthand for proxifying @getIndex@

type PRI is i = Proxy (RunningIndex (is:.i))

