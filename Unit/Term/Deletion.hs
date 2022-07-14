
module ADPfusion.Unit.Term.Deletion where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADPfusion.Core
import           ADPfusion.Unit.Core



instance
  forall m pos posLeft ls i
  . ( TermStream m (Z:.pos) (TermSymbol M Deletion) (Elm (Term1 (Elm ls (Unit i))) (Z :. Unit i)) (Z:.Unit i)
    , posLeft ~ LeftPosTy pos Deletion (Unit i)
    , TermStaticVar pos Deletion (Unit i)
    , MkStream m posLeft ls (Unit i)
    )
  ⇒ MkStream m pos (ls :!: Deletion) (Unit i) where
  mkStream pos (ls :!: Deletion) grd us is
    = S.map (\(ss,ee,ii) -> ElmDeletion ii ss)
    . addTermStream1 pos Deletion us is
    . mkStream (Proxy ∷ Proxy posLeft) ls (termStaticCheck pos Deletion us is grd) us
    $ (termStreamIndex pos Deletion is)
  {-# Inline mkStream #-}


instance
  ( TermStreamContext m ps ts s x0 i0 is (Unit I)
  , Monad m
  , (TermStream m ps ts (Elm x0 i0) is)
  ) => TermStream m ('(:.) ps p) (TermSymbol ts Deletion) s (is:.Unit I) where
  termStream Proxy (ts:|Deletion) (us:.._) (is:._)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiUnit) (ee:.()))
    . termStream (Proxy ∷ Proxy ps) ts us is
  {-# Inline termStream #-}

instance TermStaticVar (IStatic d) Deletion (Unit I) where
  termStreamIndex Proxy Deletion Unit = Unit
  termStaticCheck Proxy Deletion _ Unit grd = grd
  {-# Inline [0] termStreamIndex #-}
  {-# Inline [0] termStaticCheck #-}

