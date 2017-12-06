
module ADP.Fusion.Unit.Term.Deletion where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADP.Fusion.Core
import           ADP.Fusion.Unit.Core



instance
  forall m pos posLeft ls i
  . ( TmkCtx1 m pos ls Deletion (Unit i)
    , TermStream m ('(:.) Z pos) (TermSymbol M Deletion) (Elm (Term1 (Elm ls (Unit i))) (Z :. Unit i)) (Z:.Unit i)
    , posLeft ~ LeftPosTy pos Deletion (Unit i)
    , MkStream m posLeft ls (Unit i)
    )
  ⇒ MkStream m pos (ls :!: Deletion) (Unit i) where
  mkStream pos (ls :!: Deletion) grd us is
    = S.map (\(ss,ee,ii) -> ElmDeletion ii ss)
    . addTermStream1 pos Deletion us is
    . mkStream (Proxy ∷ Proxy posLeft) ls (grd `andI#` termStaticCheck pos Deletion is) us
    $ (termStreamIndex pos Deletion is)
  {-# Inline mkStream #-}


instance
  ( TstCtx ps m ts s x0 i0 is (Unit I)
  , Monad m
  , (TermStream m ps ts (Elm x0 i0) is)
  ) => TermStream m ('(:.) ps p) (TermSymbol ts Deletion) s (is:.Unit I) where
  termStream Proxy (ts:|Deletion) (us:.._) (is:._)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiU) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

{-
instance
  ( TstCtx m ts s x0 i0 is (Unit O)
  ) => TermStream m (TermSymbol ts Deletion) s (is:.Unit O) where
  termStream (ts:|Deletion) (cs:.OStatic ()) (us:.._) (is:._)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiU) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar Deletion (Unit I) where
  termStreamIndex _ _ _ = Unit
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Deletion (Unit O) where
  termStreamIndex _ _ _ = Unit
  {-# Inline [0] termStreamIndex #-}
-}

