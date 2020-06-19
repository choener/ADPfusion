
{-# Language MagicHash #-}

module ADPfusion.Core.Multi where

import qualified Data.Vector.Fusion.Stream.Monadic as S
import           Data.Vector.Fusion.Stream.Monadic
import           Data.Strict.Tuple
import           Data.Proxy
import           Prelude hiding (map)
import           GHC.Exts
import           Debug.Trace

import           Data.PrimitiveArray.Index.Class hiding (map)

import           ADPfusion.Core.Classes
import           ADPfusion.Core.TyLvlIx



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
  type RecElm (ls :!: TermSymbol a b) i = Elm (ls :!: TermSymbol a b) i
  getArg (ElmTS a _ ls) = getArg ls :. a
  getIdx (ElmTS _ i _ ) = i
  getElm = id
  {-# Inline [0] getArg #-}
  {-# Inline [0] getIdx #-}
  {-# Inline [0] getElm #-}

deriving instance (Show i, Show (RunningIndex i), Show (TermArg (TermSymbol a b)), Show (Elm ls i)) => Show (Elm (ls :!: TermSymbol a b) i)

type instance LeftPosTy (ps :. p) (TermSymbol a b) (is:.i) = (LeftPosTy ps a is) :. (LeftPosTy p b i)

instance
  ( Monad m
  , MkStream m posLeft ls i
  , Element ls i
  , TermStaticVar pos (TermSymbol a b) i
  , TermStream m pos (TermSymbol a b) (Elm ls i) i
  , posLeft ~ LeftPosTy pos (TermSymbol a b) i
  ) => MkStream m pos (ls :!: TermSymbol a b) i where
  mkStream Proxy (ls :!: ts) grd lu i
    = map (\(TState sS ii ee) -> ElmTS ee ii sS)
    . termStream (Proxy ∷ Proxy pos) ts lu i
    . map (\s -> TState s RiZ Z)
    $ mkStream (Proxy ∷ Proxy posLeft)
               ls
               (termStaticCheck (Proxy ∷ Proxy pos) ts lu i grd)
               lu (termStreamIndex (Proxy ∷ Proxy pos) ts i)
  {-# Inline mkStream #-}

-- | 

type instance LeftPosTy Z M Z = Z

instance Monad m => MkStream m Z S Z where
  -- mkStream Proxy S grd ZZ Z = S.filter (const $ isTrue# grd) $ S.singleton $ ElmS RiZ
  mkStream Proxy S grd ZZ Z = staticCheck# grd $ S.singleton $ ElmS RiZ
  {-# Inline mkStream #-}

-- | For multi-dimensional terminals we need to be able to calculate how the
-- static/variable signal changes and if the index for the inner part needs to
-- be modified.

class TermStaticVar pos sym ix where
--  termStaticVar   ∷ sym → Context i → i → Context i
  termStreamIndex ∷ Proxy pos → sym → ix → ix
  termStaticCheck ∷ Proxy pos → sym → LimitType ix → ix → Int# → Int#

instance TermStaticVar pos M Z where
  termStreamIndex Proxy M Z = Z
  termStaticCheck Proxy M _ Z grd = grd
  {-# INLINE [0] termStreamIndex #-}
  {-# INLINE [0] termStaticCheck #-}

instance
  ( TermStaticVar ps ts is
  , TermStaticVar p  t  i
  ) => TermStaticVar (ps:.p) (TermSymbol ts t) (is:.i) where
  termStreamIndex Proxy (ts:|t) (is:.i) = termStreamIndex (Proxy ∷ Proxy ps) ts is :. termStreamIndex (Proxy ∷ Proxy p) t i
  termStaticCheck Proxy (ts:|t) (us:..u) (is:.i) grd = termStaticCheck (Proxy ∷ Proxy ps) ts us is (termStaticCheck (Proxy ∷ Proxy p) t u i grd)
  {-# INLINE [0] termStreamIndex #-}
  {-# INLINE [0] termStaticCheck #-}

--instance RuleContext Z where
type instance InitialContext Z = Z

--instance (RuleContext is, RuleContext i) => RuleContext (is:.i) where
type instance InitialContext (is:.i) = InitialContext is:.InitialContext i

class TableStaticVar pos minSize tableIx ix where
  tableStreamIndex
    ∷ Proxy pos
    -- ^ provide type-level information on if we are currently static/variable/
    -- etc
    → minSize
    -- ^ Information on the minimal size of the corresponding table.
    → LimitType tableIx
    -- ^ provide type-level information on the index structure of the table we
    -- are looking at. This index structure might well be different than the
    -- @ix@ index we use in the grammar.
    → ix
    -- ^ current right-most index
    → ix
    -- ^ right-most index for symbol to the left of us

-- | Index "0" for multi-dimensional syntactic variables.

instance TableStaticVar pos Z tableIx Z where
  tableStreamIndex Proxy Z _ Z = Z
  {-# INLINE [0] tableStreamIndex #-}

instance
  ( TableStaticVar ps cs us is
  , TableStaticVar p  c  u  i
  )
  ⇒ TableStaticVar (ps:.p) (cs:.c) (us:.u) (is:.i) where
  tableStreamIndex Proxy (cs:.c) (us:..u) (is:.i)
    =  tableStreamIndex (Proxy ∷ Proxy ps) cs us is
    :. tableStreamIndex (Proxy ∷ Proxy p ) c  u  i
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
    , TermStream m (Z:.pos) (TermSymbol M t) (Elm (Term1 s) (Z:.i)) (Z:.i)
    )
  ⇒ Proxy pos
  → t
  → LimitType i
  → i
  → Stream m s
  → Stream m (s,TermArg t,RunningIndex i)
addTermStream1 Proxy t u i
  = map (\(TState (ElmTerm1 sS) (RiZ:.:ii) (Z:.ee)) -> (sS,ee,ii))
  . termStream (Proxy ∷ Proxy (Z:.pos)) (M:|t) (ZZ:..u) (Z:.i)
  . map (\s -> TState (elmTerm1 s i) RiZ Z)
{-# Inline addTermStream1 #-}

newtype Term1 s = Term1 s

elmTerm1 :: s -> i -> Elm (Term1 s) (Z:.i)
elmTerm1 s _ = ElmTerm1 s
{-# Inline elmTerm1 #-}

instance (s ~ Elm x0 i, Element x0 i) => Element (Term1 s) (Z:.i) where
  newtype Elm (Term1 s) (Z:.i) = ElmTerm1 s
  type Arg (Term1 s) = s
  type RecElm (Term1 s) (Z:.i) = Elm (Term1 s) (Z:.i)
  getIdx (ElmTerm1 s) = RiZ :.: getIdx s
  getArg (ElmTerm1 s) = s
  getElm  = error "Element/Term1:getElm not implemented"
  {-# Inline [0] getIdx #-}
  {-# Inline [0] getArg #-}
  {-# Inline [0] getElm #-}

-- | @Term MkStream@ context
--
-- TODO prepare for deletion

--type TermMkStreamContext m (pos ∷ k) ls t i
--  = ( Monad m
--    , MkStream m pos ls i
--    , TermStream m pos (TermSymbol M t) (Elm (Term1 (Elm ls i)) (Z:.i)) (Z:.i)
--    , Element ls i
--    , TermStaticVar pos t i
--    )

-- | @Term TermStream@ context

type TermStreamContext m (pos ∷ k) ts s x0 sixty is i
  = ( Monad m
    , TermStream m pos ts s is
    , GetIndex (RunningIndex sixty) (RunningIndex (is:.i))
    , GetIx (RunningIndex sixty) (RunningIndex (is:.i)) ~ (RunningIndex i)
    , Element x0 sixty
    , s ~ Elm x0 sixty
    )

-- | Shorthand for proxifying @getIndex@

type PRI is i = Proxy (RunningIndex (is:.i))

