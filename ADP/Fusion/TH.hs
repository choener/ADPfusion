{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}

module ADP.Fusion.TH where

import           Data.List
import           Data.Tuple.Select
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream.Monadic as SM


-- | Create the algebra product function from a signature type constructor.
--
-- TODO make the resulting function INLINE
--
-- TODO compare @ntTypes@ with the stream argument types of all @hs@ (via their
-- @hns@ names). If there is a mismatch, then either not all non-terminal types
-- have a corresponding choice function or vice versa.

makeAlgebraProductH :: [Name] -> Name -> Q [Dec]
makeAlgebraProductH hns nm = do
  rnm <- reify nm
  case rnm of
    TyConI (DataD ctx tyConName args cs d) -> case cs of
      -- we analyze the accessor functions and look for the objective function
      -- accessor. It's stream parameter is the type of the non-terminal.
      -- Everything else in accessors are terminal parameters.
      [RecC dataConName fs'] -> do
        -- split @fs@ into functions applied to rule RHSs and choice functions (@hs@)
        let (fs,hs) = partition ((`notElem` hns) . sel1) fs'
        -- the result types of the @fs@ are the types of the non-terminal symbols
        let ntTypes = nub . map getNtTypes $ fs
        runIO $ putStrLn ""
        runIO $ mapM_ print fs
        runIO $ putStrLn ""
        runIO $ mapM_ print hs
        runIO $ putStrLn ""
        runIO $ mapM_ print ntTypes
        runIO $ putStrLn ""
        l <- newName "l"
        vl <- varP l
        lvs <- sequence $ replicate (length fs') (newName "lv")
        r <- newName "r"
        rvs <- sequence $ replicate (length fs') (newName "rv")
        e <-  tupE []
        -- bind the two algebras in the where part
        -- the single clause we deal with
        let cls = clause [varP l, varP r] (normalB $ tupE [])
                    -- the body of the where part; this also fixes the type of @varP l/r@
                    [ valD (conP dataConName (map varP lvs)) (normalB $ varE l) []
                    , valD (conP dataConName (map varP rvs)) (normalB $ varE r) []
                    ]
        -- finally, we bind everything together, creating the function @(<**)@
        fun <- funD (mkName "<**") [cls]
        runIO $ print fun
        return
          [ fun -- FunD (mkName "<**") [Clause [VarP l, VarP r] (NormalB e) []] -- LamE [VarP l] (LamE [VarP r] (undefined))
          ]
      _   -> fail "more than one data ctor"
    _          -> fail "unsupported data type"

-- | Get us the 'Name' of a non-terminal type. Theses are simply the last
-- @VarT@s occuring in a function.

getNtTypes :: VarStrictType -> Name
getNtTypes = go . sel3 where
  go t
    | AppT _ (VarT x) <- t = x
    | AppT _ x        <- t = go x
    | otherwise            = error $ "undetermined error"

-- |

mkEvalFun :: [Name] -> VarStrictType -> VarStrictTypeQ
mkEvalFun ns (v,s,t) = do
  runIO $ mapM_ print ns
  return undefined

-- |

mkChoiceFun = undefined


{-
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
