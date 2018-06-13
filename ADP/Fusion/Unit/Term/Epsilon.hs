
module ADP.Fusion.Unit.Term.Epsilon where

import           Data.Proxy
import           Data.Strict.Tuple
import qualified Data.Vector.Fusion.Stream.Monadic as S
import           GHC.Exts

import           Data.PrimitiveArray

import           ADP.Fusion.Core
import           ADP.Fusion.Unit.Core



instance
  forall m pos posLeft ls i
  . ( TermStream m (Z:.pos) (TermSymbol M Epsilon) (Elm (Term1 (Elm ls (Unit i))) (Z:.Unit i)) (Z:.Unit i)
    , posLeft ~ LeftPosTy pos Epsilon (Unit i)
    , TermStaticVar pos Epsilon (Unit i)
    , MkStream m posLeft ls (Unit i)
    )
  ⇒ MkStream m pos (ls :!: Epsilon) (Unit i) where
  mkStream pos (ls :!: Epsilon) grd us is
    = S.map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 pos Epsilon us is
    . mkStream (Proxy ∷ Proxy posLeft) ls (termStaticCheck pos Epsilon is grd) us
    $ termStreamIndex pos Epsilon is
  {-# Inline mkStream #-}



--instance
--  ( TermStreamContext m ps ts s x0 i0 is (Unit I)
--  , TermStream m ps ts (Elm x0 i0) is
--  ) ⇒ TermStream m (TermSymbol ts Epsilon) s (is:.Unit I) where
--  termStream (ts:|Epsilon) (cs:.IStatic ()) (us:.._) (is:._)
--    = S.map (\(TState s ii ee) -> TState s (ii:.:RiU) (ee:.()))
--    . termStream ts cs us is
--  {-# Inline termStream #-}

{-
instance
  ( TstCtx m ts s x0 i0 is (Unit O)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.Unit O) where
  termStream (ts:|Epsilon) (cs:.OStatic ()) (us:.._) (is:._)
    = S.map (\(TState s ii ee) -> TState s (ii:.:RiU) (ee:.()))
    . termStream ts cs us is
  {-# Inline termStream #-}



instance TermStaticVar Epsilon (Unit I) where
  termStaticVar _ _ _ = IStatic ()
  termStreamIndex _ _ _ = Unit
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Epsilon (Unit O) where
  termStaticVar _ _ _ = OStatic ()
  termStreamIndex _ _ _ = Unit
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}
-}

