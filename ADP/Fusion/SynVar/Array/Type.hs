
{-# Language DataKinds #-}
{-# Language TypeOperators #-}

module ADP.Fusion.SynVar.Array.Type where

import Data.Strict.Tuple hiding (uncurry,snd)
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM)
import Debug.Trace
import Prelude hiding (map,head,mapM)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Base
import ADP.Fusion.SynVar.Backtrack
import ADP.Fusion.SynVar.Axiom
import ADP.Fusion.SynVar.Indices

import GHC.TypeLits
import Data.Proxy
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Fusion.Stream as S



-- | Immutable table.

data ITbl m arr i x where
  ITbl :: { iTblBigOrder    :: !Int
          , iTblLittleOrder :: !Int
          , iTblConstraint  :: !(TblConstraint i)
          , iTblArray       :: !(arr i x)
          , iTblFun         :: !(i -> i -> m x)
          } -> ITbl m arr i x

instance Build (ITbl m arr i x)

type instance TermArg (TermSymbol a (ITbl m arr i x)) = TermArg a :. x

instance GenBacktrackTable (ITbl mF arr i x) mF mB r where
  data Backtrack (ITbl mF arr i x) mF mB r = BtITbl !(TblConstraint i) !(arr i x) (i -> i -> mB [r])
  type BacktrackIndex (ITbl mF arr i x) = i
  toBacktrack (ITbl _ _ c arr _) _ bt = BtITbl c arr bt
  {-# Inline toBacktrack #-}

type instance TermArg (TermSymbol a (Backtrack (ITbl mF arr i x) mF mB r)) = TermArg a :. (x,[r])

instance
  ( Monad m
  , PrimArrayOps arr i x
  , IndexStream i
  ) => Axiom (ITbl m arr i x) where
  type AxiomStream (ITbl m arr i x) = m x
  axiom (ITbl _ _ c arr _) = do
    k <- (head . uncurry streamDown) $ bounds arr
    return $ arr ! k
  {-# Inline axiom #-}

instance
  ( Monad mB
  , PrimArrayOps arr i x
  , IndexStream i
  ) => Axiom (Backtrack (ITbl mF arr i x) mF mB r) where
  type AxiomStream (Backtrack (ITbl mF arr i x) mF mB r) = mB [r]
  axiom (BtITbl c arr bt) = do
    h <- (head . uncurry streamDown) $ bounds arr
    bt (snd $ bounds arr) h
  {-# Inline axiom #-}

instance Element ls i => Element (ls :!: ITbl m arr j x) i where
  data Elm    (ls :!: ITbl m arr j x) i = ElmITbl !x !i !i !(Elm ls i)
  type Arg    (ls :!: ITbl m arr j x)   = Arg ls :. x
  type RecElm (ls :!: ITbl m arr j x) i = Elm ls i
  getArg (ElmITbl x _ _ ls) = getArg ls :. x
  getIdx (ElmITbl _ i _ _ ) = i
  getOmx (ElmITbl _ _ o _ ) = o
  getElm (ElmITbl _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}
  {-# Inline getElm #-}

deriving instance (Show i, Show (Elm ls i), Show x) => Show (Elm (ls :!: ITbl m arr j x) i)

instance Element ls i => Element (ls :!: (Backtrack (ITbl mF arr j x) mF mB r)) i where
  data Elm    (ls :!: (Backtrack (ITbl mF arr j x) mF mB r)) i = ElmBtITbl !x [r] !i !i !(Elm ls i)
  type Arg    (ls :!: (Backtrack (ITbl mF arr j x) mF mB r))   = Arg ls :. (x, [r])
  type RecElm (ls :!: (Backtrack (ITbl mF arr j x) mF mB r)) i = Elm ls i
  getArg (ElmBtITbl x s _ _ ls) = getArg ls :. (x,s)
  getIdx (ElmBtITbl _ _ i _ _ ) = i
  getOmx (ElmBtITbl _ _ _ o _ ) = o
  getElm (ElmBtITbl _ _ _ _ ls) = ls
  {-# Inline getArg #-}
  {-# Inline getIdx #-}
  {-# Inline getOmx #-}
  {-# Inline getElm #-}

instance (Show x, Show i, Show (Elm ls i)) => Show (Elm (ls :!: (Backtrack (ITbl mF arr i x) mF mB r)) i) where
  show (ElmBtITbl x _ i o s) = show (x,i,o) ++ " " ++ show s

instance
  ( Monad m
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , MkStream m ls (is:.i)
  , PrimArrayOps arr (is:.i) x
  ) => MkStream m (ls :!: ITbl m arr (is:.i) x) (is:.i) where
  mkStream (ls :!: ITbl _ _ c t _) vs lu is
    = map (\(S5 s _ _ i o) -> ElmITbl (t ! i) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) lu (tableStreamIndex c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (is:.i)
  , TableStaticVar (is:.i)
  , TableIndices (is:.i)
  , MkStream mB ls (is:.i)
  , PrimArrayOps arr (is:.i) x
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr (is:.i) x) mF mB r) (is:.i) where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = mapM (\(S5 s _ _ i o) -> bt us i >>= \ ~bb -> return $ ElmBtITbl (t ! i) (bb {-bt us i-}) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) us (tableStreamIndex c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad m
  , Element ls (Outside (is:.i))
  , TableStaticVar (Outside (is:.i))
  , TableIndices (Outside (is:.i))
  , MkStream m ls (Outside (is:.i))
  , PrimArrayOps arr (Outside (is:.i)) x
  , Show (is:.i)
  ) => MkStream m (ls :!: ITbl m arr (Outside (is:.i)) x) (Outside (is:.i)) where
  mkStream (ls :!: ITbl _ _ c t _) vs lu is
    = map (\(S5 s _ _ i o) -> ElmITbl (t ! o) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) lu (tableStreamIndex c vs is)
  {-# Inline mkStream #-}

instance
  ( Monad mB
  , Element ls (Outside (is:.i))
  , TableStaticVar (Outside (is:.i))
  , TableIndices (Outside (is:.i))
  , MkStream mB ls (Outside (is:.i))
  , PrimArrayOps arr (Outside (is:.i)) x
  , Show (is:.i)
  ) => MkStream mB (ls :!: Backtrack (ITbl mF arr (Outside (is:.i)) x) mF mB r) (Outside (is:.i)) where
  mkStream (ls :!: BtITbl c t bt) vs us is
    = mapM (\(S5 s _ _ i o) -> bt us o >>= \bb -> return $ ElmBtITbl (t ! o) (bb {-bt us o-}) i o s)
    . tableIndices c vs is
    . map (\s -> S5 s Z Z (getIdx s) (getOmx s))
    $ mkStream ls (tableStaticVar vs is) us (tableStreamIndex c vs is)
  {-# Inline mkStream #-}



-- * Playground: simplify index generation

class GetIndex ixTy myTy (cmp :: Ordering) where
  type ResolvedIx ixTy myTy cmp :: *
  getIndex :: ixTy -> (Proxy myTy) -> (Proxy cmp) -> ResolvedIx ixTy myTy cmp

instance GetIndex (ix:.i) (my:.m) EQ where
  type ResolvedIx (ix:.i) (my:.m) EQ = i
  getIndex (ix:.i) _ _ = i
  {-# Inline getIndex #-}

instance (GetIndex ix (my:.m) (CmpNat (ToNat ix) (ToNat (my:.m)))) => GetIndex (ix:.i) (my:.m) GT where
  type ResolvedIx (ix:.i) (my:.m) GT = ResolvedIx ix (my:.m) (CmpNat (ToNat ix) (ToNat (my:.m)))
  getIndex (ix:._) p _ = getIndex ix p (Proxy :: Proxy (CmpNat (ToNat ix) (ToNat (my:.m))))
  {-# Inline getIndex #-}

instance (GetIndex ix Z (CmpNat (ToNat ix) (ToNat Z))) => GetIndex (ix:.i) Z GT where
  type ResolvedIx (ix:.i) Z GT = ResolvedIx ix Z (CmpNat (ToNat ix) (ToNat Z))
  getIndex (ix:._) p _ = getIndex ix p (Proxy :: Proxy (CmpNat (ToNat ix) (ToNat Z)))
  {-# Inline getIndex #-}

instance GetIndex Z Z EQ where
  type ResolvedIx Z Z EQ = Z
  getIndex _ _ _ = Z
  {-# Inline getIndex #-}

ggg :: forall ixTy myTy . GetIndex ixTy myTy (CmpNat (ToNat ixTy) (ToNat myTy)) => ixTy -> Proxy myTy -> ResolvedIx ixTy myTy (CmpNat (ToNat ixTy) (ToNat myTy))
ggg ixTy myTy = getIndex ixTy (Proxy :: Proxy myTy) (Proxy :: Proxy (CmpNat (ToNat ixTy) (ToNat myTy)))
{-# Inline ggg #-}

type family ToNat x :: Nat

type instance ToNat Z       = 0
type instance ToNat (is:.i) = ToNat is + 1

testggg :: (Z:.Int:.Char) -> Int
testggg ab = ggg ab (Proxy :: Proxy (Z:.Int)) --  (Z:.(3::Int))
{-# NoInline testggg #-}

class AddIndex a i where
  addIndex :: (Monad m, GetIndex a i (CmpNat (ToNat a) (ToNat i)) ) => TblConstraint i -> Context i -> i -> Stream m (s,a,a,Z,Z) -> Stream m (s,a,a,i,i)

instance
  ( AddIndex a is
  , GetIndex a is (CmpNat (ToNat a) (ToNat is))
  , ResolvedIx a (is:.Subword) (CmpNat (ToNat a) (ToNat (is:.Subword))) ~ Subword
  ) => AddIndex a (is:.Subword) where
  addIndex (cs:._) (vs:.IStatic _) (is:.Subword (i:.j))
    = map (\(s,a,b,y,z) -> let (Subword (u:.v)) = ggg a (Proxy :: Proxy (is:.Subword))
                               (Subword (w:.x)) = ggg b (Proxy :: Proxy (is:.Subword))
                           in (s,a,b,y:.subword u v,z:.subword w x)
          ) . addIndex cs vs is
  {-# Inline addIndex #-}

instance AddIndex a Z where
  addIndex _ _ _ = id
  {-# Inline addIndex #-}

addIndex' :: (Monad m, AddIndex a i, GetIndex a i (CmpNat (ToNat a) (ToNat i)), s ~ Elm x0 a, Element x0 a) => TblConstraint i -> Context i -> i -> Stream m s -> Stream m (s,a,a,i,i)
addIndex' t c i = addIndex t c i . map (\s -> (s,getIdx s, getOmx s, Z,Z))
{-# Inline addIndex' #-}

testAddIndex i j =
  let (_,_,_,(Z:.Subword (a:.b):.Subword (c:.d)),_) = S.head
                                                    $ addIndex' (Z:.EmptyOk:.EmptyOk) (Z:.IStatic undefined :.IStatic undefined) (Z:.subword i (2*i):.subword j (3*j))
                                                    $ S.singleton
                                                    $ ElmS (Z:.subword (4*i) (5*i):.subword (6*j) (7*j)) (Z:.subword 0 0:.subword 0 0)
  in  (a,b,c,d)
{-# NoInline testAddIndex #-}

