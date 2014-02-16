{-# LANGUAGE NoMonomorphismRestriction #-}
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
        fun <- funD (mkName "<**") [genClause dataConName fs' fs hs]
        --runIO $ print fun
        return
          [ fun -- FunD (mkName "<**") [Clause [VarP l, VarP r] (NormalB e) []] -- LamE [VarP l] (LamE [VarP r] (undefined))
          ]
      _   -> fail "more than one data ctor"
    _          -> fail "unsupported data type"

-- | Build the single clause of our function. We shall need the functions bound
-- in the where part to create the joined functions we need to return.

-- genClause :: ?
genClause conName allFunNames evalFunNames choiceFunName = do
  let nonTermNames = nub . map getNtTypes $ evalFunNames
  -- bind the l'eft and r'ight variable of the two algebras we want to join,
  -- also create unique names for the function names we shall bind later.
  nameL <- newName "l"
  varL  <- varP nameL
  fnmsL <- sequence $ replicate (length allFunNames) (newName "fnamL")
  nameR <- newName "r"
  varR  <- varP nameR
  fnmsR <- sequence $ replicate (length allFunNames) (newName "fnamR")
  -- bind the individual variables in the where part
  whereL <- valD (conP conName (map varP fnmsL)) (normalB $ varE nameL) []
  whereR <- valD (conP conName (map varP fnmsR)) (normalB $ varE nameR) []
  rce <- recConE conName
          $ zipWith3 (genEvalFunction nonTermNames) fnmsL fnmsR evalFunNames
  -- build the function pairs
  -- to keep our sanity, lets print this stuff
  let cls = Clause [varL, varR] (NormalB rce) [whereL,whereR]
  return cls

-- |
--
-- TODO need fun names from @l@ and @r@

--genEvalFunction :: [Name] -> z1 -> z2 VarStrictType -> Q (Name,Exp)
genEvalFunction nts fL fR (name,_,t) = do
  runIO $ print $ getNames t
  (lamPat,funL,funR) <-recBuildLamPat nts fL fR $ init $ getNames t -- @init@ since we don't want the result as a parameter
  let exp = LamE lamPat $ TupE [funL,funR]
  runIO $ print exp
  return (name,exp)

-- |

recBuildLamPat :: [Name] -> Name -> Name -> [Name] -> Q ([Pat], Exp, Exp)
recBuildLamPat nts fL' fR' t = go ([],VarE fL',VarE fR') t where
  go tpl [] = return tpl
  go (ls,fL,fR) (x:xs)
    | x `elem` nts = do nX  <- newName "nX"
                        nYs <- newName "nYs"
                        lmb <- tupP [varP nX, varP nYs]
                        ffL <- appE (return fL) (varE nX)
                        -- something concatmap like
                        ffR <- tupE []
                        go (ls++[lmb],ffL,ffR) xs
    | otherwise    = do n   <- newName "t"
                        lmb <- sigP (varP n) (varT x)
                        ffL <- appE (return fL) (varE n)
                        ffR <- appE (appE [| \r -> return . SM.map (\f -> f r) |] (varE n)) (return fR)
                        go (ls++[lmb],ffL,ffR) xs

-- |

getNames t = go t where
  go t
    | VarT x <- t = [x]
    | AppT (AppT ArrowT (VarT x)) y <- t = x : go y
    | otherwise            = error $ "undetermined error:" ++ show t


-- | Get us the 'Name' of a non-terminal type. Theses are simply the last
-- @VarT@s occuring in a function.

getNtTypes :: VarStrictType -> Name
getNtTypes vst = go $ sel3 vst where
  go t
    | AppT _ (VarT x) <- t = x
    | AppT _ x        <- t = go x
    | otherwise            = error $ "undetermined error:" ++ show vst

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
