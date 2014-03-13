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
genClause conName allFunNames evalFunNames choiceFunNames = do
  let nonTermNames = nub . map getNtTypes $ evalFunNames
  -- bind the l'eft and r'ight variable of the two algebras we want to join,
  -- also create unique names for the function names we shall bind later.
  nameL <- newName "l"
  varL  <- varP nameL
  -- TODO fnmsL,R makes the implicit assumption that function names come first,
  -- then choice functions; we need to fix that!
  fnmsL <- sequence $ replicate (length allFunNames) (newName "fnamL")
  nameR <- newName "r"
  varR  <- varP nameR
  fnmsR <- sequence $ replicate (length allFunNames) (newName "fnamR")
  -- bind the individual variables in the where part
  whereL <- valD (conP conName (map varP fnmsL)) (normalB $ varE nameL) []
  whereR <- valD (conP conName (map varP fnmsR)) (normalB $ varE nameR) []
  rce <- recConE conName
          $  zipWith3 (genChoiceFunction) (drop (length evalFunNames) fnmsL) (drop (length evalFunNames) fnmsR) choiceFunNames
          ++ zipWith3 (genEvalFunction nonTermNames) fnmsL fnmsR evalFunNames
  -- build the function pairs
  -- to keep our sanity, lets print this stuff
  let cls = Clause [varL, varR] (NormalB rce) [whereL,whereR]
  return cls

genChoiceFunction hL hR (name,_,t) = do
  runIO $ print (hL,hR,name)
  (lamPat,funH) <- buildChoice hL hR
  let exp = LamE lamPat $ funH
  return (name,exp)

-- |
--
-- TODO need fun names from @l@ and @r@

--genEvalFunction :: [Name] -> z1 -> z2 VarStrictType -> Q (Name,Exp)
genEvalFunction nts fL fR (name,_,t) = do
  --runIO $ print $ getNames t
  (lamPat,funL,funR) <-recBuildLamPat nts fL fR $ init $ getNames t -- @init@ since we don't want the result as a parameter
  let exp = LamE lamPat $ TupE [funL,funR]
  --runIO $ print exp
  return (name,exp)

-- |

recBuildLamPat :: [Name] -> Name -> Name -> [Name] -> Q ([Pat], Exp, Exp)
recBuildLamPat nts fL' fR' t = go True ([],VarE fL',VarE fR') t where
  go True  tpl [] = error "recBuildLamPat: no arguments"
  go False (ls,fL,fR) [] = do ffR <- appE [| return |] (return fR)
                              return (ls,fL,fR)
  go True  (ls,fL,fR) xs = do ffR <- appE [| SM.singleton |] (return fR)
                              go False (ls,fL,ffR) xs
  go False (ls,fL,fR) (x:xs)
    | x `elem` nts = do nX  <- newName "nX"
                        nYs <- newName "nYs"
                        lmb <- tupP [varP nX, varP nYs]
                        ffL <- appE (return fL) (varE nX)
                        ffR <- appE (appE [| \ys fs -> SM.concatMap (\f -> SM.map f ys) fs |] (varE nYs)) (return fR)
                        go False (ls++[lmb],ffL,ffR) xs
    | otherwise    = do n   <- newName "t"
                        lmb <- sigP (varP n) (varT x) -- we actually have a signature, nice
                        ffL <- appE (return fL) (varE n)
                        ffR <- appE (appE [| \r -> SM.map (\f -> f r) |] (varE n)) (return fR)
                        go False (ls++[lmb],ffL,ffR) xs

buildChoice :: Name -> Name -> Q ([Pat], Exp)
buildChoice hL' hR' = do
  hL   <- varE hL'
  hR   <- varE hR'
  hcmb <- [| \hL hR xs -> (hL $ SM.map fst xs) >>= \cl -> (hR $ SM.concatMapM snd $ SM.filter ((cl==).fst) $ xs) |]
  happ <- appE (appE (return hcmb) (return hL)) (return hR)
  n    <- newName "xs"
  lmb  <- varP n
  return ([lmb],happ)

-- |

getNames t = go t where
  go t
    | VarT x <- t = [x]
    | AppT (AppT ArrowT (VarT x)) y <- t = x : go y
--    | AppT (AppT ArrowT (TupleT 0)) y <- t = go y
--    | ForallT _ _ x <- t = go x
    | otherwise            = error $ "getNames error: " ++ show t


-- | Get us the 'Name' of a non-terminal type. Theses are simply the last
-- @VarT@s occuring in a function.

getNtTypes :: VarStrictType -> Name
getNtTypes vst = go $ sel3 vst where
  go t
    | AppT _ (VarT x) <- t = x
    | AppT _ x        <- t = go x
    | otherwise            = error $ "undetermined error:" ++ show vst

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
