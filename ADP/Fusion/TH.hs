{-# LANGUAGE TemplateHaskell #-}

module ADP.Fusion.TH where

import           Data.List
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream.Monadic as SM



{-

-- | Create the algebra product function from a signature type constructor.

makeAlgebraProduct :: Name -> Q [Dec]
makeAlgebraProduct nm = do
  rnm <- reify nm
  case rnm of
    TyConI (DataD ctx tyConName args cs d) -> case cs of
      -- we analyze the accessor functions and look for the objective function
      -- accessor. It's stream parameter is the type of the non-terminal.
      -- Everything else in accessors are terminal parameters.
      [RecC dataConName fs] -> do
        -- find the objective function type (we crash if the user has more than
        -- one)
        let [oF] = filter (isObjectiveF . sel3) fs
        error $ unlines $ intersperse "\n" $ map show fs
      _   -> fail "more than one data ctor"
    _          -> fail "unsupported data type"

sel3 (a,b,c) = c

zzz :: VarStrictType -> String
zzz (nm,s,t) = show (nm,s,t)

isObjectiveF :: Type -> Bool
isObjectiveF (AppT (AppT ArrowT (AppT (AppT (ConT s) _) _)) (AppT _ _)) | s == ''SM.Stream = True
isObjectiveF _ = False

-}

-- AppT (AppT ArrowT
--            (AppT (AppT (ConT Data.Vector.Fusion.Stream.Monadic.Stream)
--                        (VarT m_1627401654)
--                  )
--            (VarT x_1627401655)
--            )
--      )
--      (AppT (VarT m_1627401654) (VarT r_1627401656))
