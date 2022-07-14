
-- | Backtracking which uses lists internally. The basic idea is to convert
-- each @Stream@ into a list. The consumer consumes the stream lazily, but
-- allows for fusion to happen. The hope is that this improves total
-- performance in those cases, where backtracking has significant costs.

module ADPfusion.Core.TH.Backtrack where

import           Control.Applicative ( (<$>) )
import           Control.Monad
import           Control.Monad.Primitive (PrimState, PrimMonad)
import           Data.List
import           Data.Tuple.Select
import           Data.Vector.Fusion.Stream.Monadic (Stream(..))
import           Debug.Trace
import           Language.Haskell.TH
import           Language.Haskell.TH.Instances
import           Language.Haskell.TH.Syntax
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import qualified Data.Vector.Mutable as VM
import qualified Data.Set as S

import           Data.PrimitiveArray.Index.Class ( (:.)(..) , Z(..) )

import           ADPfusion.Core.TH.Common

import Control.Monad.Reader



-- | @Backtracking@ products of @f@ and @b@. Choice in @f@ needs to be
-- reduced to a scalar value. It is then compared to the @fst@ values
-- in @b@. From those, @choice b@ selects.

class ProductBacktracking sigF sigB where
  type SigBacktracking sigF sigB :: *
  (<||) :: sigF -> sigB -> SigBacktracking sigF sigB

-- | The ADP-established product operation. Returns a vector of results,
-- along the lines of what the ADP @f *** b@ provides.
--
-- @f **> g@ assumes a vector-to-vector function @f@, and
-- a vector-to-scalar function @g@.

class ProductCombining sigF sigB where
  type SigCombining sigF sigB :: *
  (**>) :: sigF -> sigB -> SigCombining sigF sigB

-- | Creates instances for all products given a signature data type.

makeProductInstances :: Name -> Q [Dec]
makeProductInstances tyconName = do
  t <- reify tyconName
  case t of
#if MIN_VERSION_template_haskell(2,11,0)
    TyConI (DataD ctx tyConName args maybeKind cs d) -> do
#else
    TyConI (DataD ctx tyConName args cs d) -> do
#endif
      let m = getMonadName args
      case cs of
        [RecC dataconName funs] -> do
          let Just (h,m',x,r) = getObjectiveNames funs
          mL <- newName "mL"
          xL <- newName "xL"
          rL <- newName "rL"
          mR <- newName "mR"
          xR <- newName "xR"
          rR <- newName "rR"
          let lType    = buildRightType tyconName (m', x, r) (mL, xL, rL)    args
          let rType    = buildRightType tyconName (m', x, r) (mR, xR, rR)    args
          let (fs,hs) = partition ((`notElem` [h]) . sel1) funs
          sigBType <- buildSigBacktrackingType  tyconName (m', x, r) xL (mR, xR, rR) args
          Clause psB (NormalB bB) dsB <- genAlgProdFunctions buildBacktrackingChoice dataconName funs fs hs
          iB <- [d| instance (Monad $(varT mL), Monad $(varT mR), Eq $(varT xL), $(varT mL) ~ $(varT mR), $(varT xL) ~ $(varT rL))
                      => ProductBacktracking $(return lType) $(return rType) where
                          type SigBacktracking $(return lType) $(return rType) = $(return sigBType)
                          (<||) = $(return $ LamE psB $ LetE dsB bB)
                          {-# Inline (<||) #-}
                |]
          -- TODO might well be that this doesn't work because we re-use
          -- type names ...
          vG <- newName "vG"
          sigPType <- buildSigCombiningType tyconName vG (m', x, r) (mL, xL, rL) (mR, xR, rR) args
          Clause psC (NormalB bC) dsC <- genAlgProdFunctions buildCombiningChoice    dataconName funs fs hs
          iC <- [d| instance (Monad $(varT mL), Monad $(varT mR), Eq $(varT xL), Ord $(varT xL), Ord $(varT xR), $(varT mL) ~ $(varT mR) ) -- , VG.Vector $(varT vG) ($(varT rL),$(varT rR)) )
                      => ProductCombining $(return lType) $(return rType) where
                          type SigCombining $(return lType) $(return rType) = $(return sigPType)
                          (**>) = $(return $ LamE psC $ LetE dsC bC)
                          {-# Inline (**>) #-}
                |]
          return $ iB ++ iC

-- | Returns the 'Name' of the monad variable.

getMonadName :: [TyVarBndr flag] -> Maybe Name
getMonadName = go
  where go [] = Nothing
        go (KindedTV m f (AppT (AppT ArrowT StarT) StarT) : _) = Just m
        go (_ : xs) = go xs

-- | Returns the 'Name's of the objective function variables, as well as
-- the name of the objective function itself.

getObjectiveNames :: [VarStrictType] -> Maybe (Name,Name,Name,Name)
getObjectiveNames = go
  where go [] = Nothing
        go ( (hName , _ , (AppT (AppT ArrowT (AppT (AppT (ConT streamName) (VarT mS)) (VarT x))) (AppT (VarT mR) (VarT r)))) : xs)
          | streamName == ''Stream && mS == mR = Just (hName,mS,x,r)
          | otherwise             = go xs
        go ( _ : xs) = go xs



-- * Constructions for the different algebra types.

-- | The left algebra type. Assumes that in @choice :: Stream m x -> m r@
-- we have that @x ~ r@.

buildLeftType :: Name -> (Name, Name, Name) -> (Name, Name) -> [TyVarBndr flag] -> Type
buildLeftType tycon (m, x, r) (mL, xL) = foldl AppT (ConT tycon) . map (VarT . go)
  where go (PlainTV z f)
          | z == m        = mL  -- correct monad name
          | z == x        = xL  -- point to new x type
          | z == r        = xL  -- stream and return type are the same
          | otherwise     = z   -- everything else can stay as is
        go (KindedTV z f _) = go (PlainTV z f)

-- | Here, we do not set any restrictions on the types @m@ and @r@.

buildRightType :: Name -> (Name, Name, Name) -> (Name, Name, Name) -> [TyVarBndr flag] -> Type
buildRightType tycon (m, x, r) (mR, xR, rR) = foldl AppT (ConT tycon) . map (VarT . go)
  where go (PlainTV z f)
          | z == m    = mR  -- have discovered a monadic type
          | z == x    = xR  -- have discovered a type that is equal to the stream type (and hence we have a synvar type)
          | z == r    = rR  -- have discovered a type that is equal to the result type (for @<||@) equal to the stream type, hence synvar
          | otherwise = z   -- this is a terminal or a terminal stack (we don't care)
        go (KindedTV z f _) = go (PlainTV z f)

-- | Build up the type for backtracking. We want laziness in the right
-- return type. Hence, we have @AppT ListT (VarT xR)@ ; i.e. we want to
-- return results in a list.

buildSigBacktrackingType :: Name -> (Name, Name, Name) -> (Name) -> (Name, Name, Name) -> [TyVarBndr flag] -> TypeQ
buildSigBacktrackingType tycon (m, x, r) (xL) (mR, xR, rR) = foldl appT (conT tycon) . map go
  where go (PlainTV z f)
          | z == m    = varT mR
          | z == x    = [t| ($(varT xL) , [ $(varT xR) ] ) |]
          | z == r    = varT rR
          | otherwise = varT z
        go (KindedTV z f _) = go (PlainTV z f)

-- |
--
-- [1] we want a list for @[xR]@ because this will make it lazy here. At
-- least that was the reason for backtracking. For forward mode, we may not
-- want this. We will have to change the function combination then?

buildSigCombiningType :: Name -> Name -> (Name, Name, Name) -> (Name, Name, Name) -> (Name, Name, Name) -> [TyVarBndr flag] -> TypeQ
buildSigCombiningType tycon vG (m, x, r) (mL, xL, rL) (mR, xR, rR) = foldl appT (conT tycon) . map go
  where go (PlainTV z f)
          | z == m    = varT mR
          | z == x    = [t| ($(varT xL) , [ $(varT xR) ] ) |]   -- [1]
          | z == r    = [t| V.Vector ($(varT rL) , $(varT rR)) |]
          | otherwise = varT z
        go (KindedTV z f _) = go (PlainTV z f)



-- *

-- | Build up attribute and choice function. Here, we actually bind the
-- left and right algebra to @l@ and @r@.

genAlgProdFunctions
  :: Choice
  -> Name
  -> [VarStrictType]
  -> [VarStrictType]
  -> [VarStrictType]
  -> Q Clause
genAlgProdFunctions choice conName allFunNames evalFunNames choiceFunNames = do
  let nonTermNames = nub . map getRuleResultType $ evalFunNames
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
          $  zipWith3 (genChoiceFunction choice) (drop (length evalFunNames) fnmsL) (drop (length evalFunNames) fnmsR) choiceFunNames
          ++ zipWith3 (genAttributeFunction nonTermNames) fnmsL fnmsR evalFunNames
  -- build the function pairs
  -- to keep our sanity, lets print this stuff
  let cls = Clause [varL, varR] (NormalB rce) [whereL,whereR]
  return cls

-- | Simple wrapper for creating the choice fun expression.

genChoiceFunction
  :: Choice
  -> Name
  -> Name
  -> VarStrictType
  -> Q (Name,Exp)
genChoiceFunction choice hL hR (name,_,t) = do
  exp <- choice hL hR
  return (name,exp)


-- | We take the left and right function name for one attribute and build
-- up the combined attribute function. Mostly a wrapper around
-- 'recBuildLampat' which does the main work.
--
-- TODO need fun names from @l@ and @r@

genAttributeFunction
  :: [Name]
  -> Name
  -> Name
  -> VarStrictType
  -> Q (Name,Exp)
genAttributeFunction nts fL fR (name,_,t) = do
  (lamPat,funL,funR) <-recBuildLamPat nts fL fR (init $ getRuleSynVarNames nts t) -- @init@ since we don't want the result as a parameter
#if MIN_VERSION_template_haskell(2,16,0)
  let exp = LamE lamPat $ TupE [Just funL, Just funR]
#else
  let exp = LamE lamPat $ TupE [funL,funR]
#endif
  return (name,exp)

-- | Now things become trickly. We are given all non-terminal names (to
-- differentiate between a terminal (stack) and a syntactic variable; the
-- left and right function; and the arguments to this attribute function
-- (except the result parameter). We are given the latter as a result to an
-- earlier call to 'getRuleSynVarNames'.
--
-- We now look at each argument and determine wether it is a syntactic
-- variable. If so, then we actually have a tuple arguments @(x,ys)@ where
-- @x@ has to optimized value and @ys@ the backtracking list. The left
-- function receives just @x@ in this case. For the right function, things
-- are more complicated, since we have to flatten lists. See 'buildRns'.
--
-- Terminals are always given "as is" since we do not have a need for
-- tupled-up information as we have for syntactic variables.

recBuildLamPat
  :: [Name]   -- ^ all non-terminal names
  -> Name     -- ^ left attribute function
  -> Name     -- ^ right attribute function
  -> [ArgTy Name]  -- ^ all arguments to the attribute function
  -> Q ([Pat], Exp, Exp)
recBuildLamPat nts fL' fR' ts = do
  -- here we just run through all arguments, either creating an @x@ and
  -- a @ys@ for a non-term or a @t@ for a term.
  ps <- mapM argTyArgs ts
  lamPat <- buildLamPat ps
  lfun <- buildLns (VarE fL') ps -- foldl buildLfun (varE fL') ps
  rfun <- buildRns (VarE fR') ps
  return (lamPat, lfun, rfun)

buildLamPat :: [ArgTy Pat] -> Q [Pat]
buildLamPat = mapM go where
  go (SynVar      p ) = return p
  go (Term        p ) = return p
  go (StackedVars ps) = build ps
  build :: [ArgTy Pat] -> Q Pat
  build = foldl (\s v -> [p| $(s) :. $(return v) |]) [p|Z|] . map get
  get :: ArgTy Pat -> Pat
  get (SynVar p) = p
  get (Term   p) = p

-- | Look at the argument type and build the capturing variables. In
-- particular captures synvar arguments with a 2-tuple @(x,ys)@.

argTyArgs :: ArgTy Name -> Q (ArgTy Pat)
argTyArgs (SynVar n) = SynVar <$> tupP [newName "x" >>= varP , newName "ys" >>= varP]
argTyArgs (Term n)          = Term <$> (newName "t" >>= varP)
argTyArgs (StackedTerms _)  = Term <$> (newName "t" >>= varP) -- !!!
argTyArgs (StackedVars vs)  = StackedVars <$> mapM argTyArgs vs
argTyArgs NilVar            = Term <$> (newName "t" >>= varP)
argTyArgs (Result _)        = error "argTyArgs: should not receive @Result@"

buildLns
  :: Exp
  -> [ArgTy Pat]
  -> ExpQ
buildLns f' ps = foldl go (return f') ps
  where go :: ExpQ -> ArgTy Pat -> ExpQ
        go f (SynVar      (TupP [VarP v,_])) = appE f (varE v)
        go f (Term        (VarP v         )) = appE f (varE v)
        go f (StackedVars vs               ) = appE f (build vs)
        build :: [ArgTy Pat] -> ExpQ
        build = foldl (\s v -> [| $(s) :. $(varE v) |]) [|Z|] . map get
        get (SynVar (TupP [VarP v,_])) = v
        get (Term   (VarP t)         ) = t

-- | Build the right-hand side of a function combined in @f <|| g@. This
-- splits the paired synvars @(x,xs)@ such that we calculate @f x@ and @g
-- xs@.
--
-- NOTE If we want to write
--
-- @
-- [ f x | x <- xs ]
-- @
--
-- then in template haskell, this looks like this:
--
-- @
-- CompE [BindS (VarP x) (VarE xs), NoBindS (AppE (VarE f) (VarE x))]
-- @
--
-- The @NoBindS@ is the final binding of @f@ to the individual @x@'s, while
-- the prior @x <- xs@ comes from @BindS (VarP x) (VarE xs)@.
--
-- TODO This is where we might be able to improve performance if we can
-- optimize @[f x y | x <- xs, y <- ys]@ for @concatMap@ in @vector@.

buildRns
  :: Exp
--  -> [Name]
  -> [ArgTy Pat]
  -> ExpQ
buildRns f' ps = do
  -- get all synvars, shallow or deep and create a new name to bind
  -- individual parts to.
  sy :: M.Map Pat Name <- M.fromList <$> (mapM (\s -> newName "y" >>= \y -> return (s,y)) $ concatMap flattenSynVars ps)
  -- bind them for the right part of the list expression (even though they
  -- are left in @CompE@. We don't use @sy@ directly to keep the order in
  -- which the comprehensions run.
  let rs = map (\k@(TupP [_,VarP v]) -> BindS (VarP $ sy M.! k) (VarE v)) $ concatMap flattenSynVars ps
  let go :: ExpQ -> ArgTy Pat -> ExpQ
      go f (SynVar      k       ) = appE f (varE $ sy M.! k) -- needed like this, because we need the @y@ in @y <- ys@
      go f (Term        (VarP v)) = appE f (varE v)
      go f (StackedVars vs      ) = appE f (foldl build [|Z|] vs)
      build :: ExpQ -> ArgTy Pat -> ExpQ
      build s (SynVar k       ) = [| $(s) :. $(varE $ sy M.! k) |]
      build s (Term   (VarP v)) = [| $(s) :. $(varE v)          |]
  funApp <- foldl go (return f') ps
  return . CompE $ rs ++ [NoBindS funApp]


-- | Type for backtracking functions.
--
-- Not too interesting, mostly to keep track of @choice@.

type Choice = Name -> Name -> Q Exp

-- | Build up the backtracking choice function. This choice function will
-- backtrack based on the first result, then return only the second.
--
-- TODO it should be (only?) this function we will need to modify to build
-- all algebra products.
--
-- @ysM@ can't be unboxed, as @snd@ of each element is a list, lazily
-- consumed. We build up @ysM@ as this makes fusion happen. Of course, this
-- is a boxed vector and not as efficient, but we gain the ability to have
-- lazily created backtracking from this!
--
-- This means strict optimization AND lazy backtracking
--
-- TODO in principle, we do more work than necessary. The line
-- @hFres <- ...@ evaluates the optimal choice from the @fst@ elements
-- again. As long as the cost is small compared to the evaluation of @snd@
-- (or the list-comprehension based creation of all parses), this won't
-- matter much.

buildBacktrackingChoice :: Choice
buildBacktrackingChoice hL' hR' =
  [| \xs -> do
      -- turn the stream into a list
      ysM <- SM.toList xs
      -- based only on the @fst@ elements, select optimal value
      hFres <- $(varE hL') $ SM.map fst $ SM.fromList ysM
      -- filter accordingly
      $(varE hR') $ SM.fromList $ concatMap snd $ filter ((hFres==) . fst) $ ysM
  |]

-- | We assume parses of type @(x,y)@ in a vector @<(x,y)>@. the function
-- acting on @x@ will produce a subset @<x>@ (in vector form). the function
-- acting on @y@ produces scalars @y@. We have @actFst :: <x> -> <x>@ and
-- @actSnd :: <y> -> y@. This in total should yield @<(x,y)> -> <(x,y)>@.
--
-- TODO This should create @generic@ vectors, that are specialized by the
-- table they are stored into.

buildCombiningChoice :: Choice
buildCombiningChoice hL' hR' =
  [| \xs -> do
      -- -- lets begin with the list of parses
      -- ys <- SM.toList xs
      -- -- but now, we actually get a list of co-optimals to keep. Yes,
      -- -- a @[fst]@ list.
      -- cooptFsts <- S.fromList <$> ( ( $(varE hL') $ SM.map fst $ SM.fromList ys ) >>= SM.toList )
      -- -- now we create a map with all the coopts, where we collect in the
      -- -- value parts the list of parses for each co-optimal @snd@ for
      -- -- a @fst@.
      -- let cooptMap = M.fromListWith (++) [ y | y <- ys, y `S.member` cooptFsts ]
      -- -- We now need to map @actSnd@ over the resulting intermediates
      -- actSnd <- mapM (\y -> $(varE hR') (SM.fromList y)) cooptMap
      -- -- a vector with co-optimals, each one associated with its optimal
      -- -- @snd@.
      -- return . VG.fromList . M.toList $ actSnd
      return undefined
  |]

-- | Turn a stream into a vector.
--
-- TODO need to be improved in terms of performance.

streamToVectorM :: (Monad m, VG.Vector v a) => SM.Stream m a -> m (v a)
streamToVectorM s = SM.toList s >>= return . VG.fromList
{-# Inline streamToVectorM #-}

-- | Gets the names used in the evaluation function. This returns one
-- 'Name' for each variable.
--
-- In case of @TupleT 0@ the type is @()@ and there isn't a name to go with
-- it. We just @mkName "()"@ a name, but this might be slightly dangerous?
-- (Not really sure if it indeed is)
--
-- With @AppT _ _@ we have a multidim terminal and produce another hackish
-- name to be consumed above.
--
-- @
-- AppT (AppT ArrowT (AppT (AppT (ConT Data.Array.Repa.Index.:.) (AppT (AppT (ConT Data.Array.Repa.Index.:.) (ConT Data.Array.Repa.Index.Z)) (VarT c_1627675270))) (VarT c_1627675270))) (VarT x_1627675265)
-- @

getRuleSynVarNames :: [Name]-> Type -> [ArgTy Name] -- [Name]
getRuleSynVarNames nts t' = go t' where
  go t
    | VarT x <- t                          = [Result x]
    | AppT (AppT ArrowT (VarT x)  ) y <- t = (if x `elem` nts then SynVar x else Term x) : go y
    | AppT (AppT ArrowT (TupleT 0)) y <- t = NilVar : go y
    | AppT (AppT ArrowT s         ) y <- t = stacked s : go y
    | otherwise                            = error $ "getRuleSynVarNames error: " ++ show t ++ "    in:    " ++ show t'
  stacked s = if null [ () | SynVar _ <- xs ] then StackedTerms xs else StackedVars xs
    where xs = reverse $ stckd s
          stckd (ConT z) | z == ''Z = []
          stckd (AppT a (TupleT 0)) = NilVar : stckd a
          stckd (AppT a (VarT x)  ) = (if x `elem` nts then SynVar x else Term x) : stckd a
          stckd (AppT (ConT c) a  ) | c == ''(:.) = stckd a
          stckd err = error $ "stckd" ++ show err

{-
(AppT (AppT (ConT Data.PrimitiveArray.Index.Class.:.)
            (AppT (AppT (ConT Data.PrimitiveArray.Index.Class.:.)
                        (ConT Data.PrimitiveArray.Index.Class.Z)
                  )
                  (VarT x_1627774371)
            )
      )
      (TupleT 0)
)
-}


data ArgTy x
  -- | This @SynVar@ spans the full column of tapes; i.e. it is a normal
  -- syntactic variable.
  = SynVar { synVarName :: x }
  -- | We have just a single-tape grammar and as such just
  -- a single-dimensional terminal. We call this term, because
  -- @StackedTerms@ will be rewritten to just @Term@!
  | Term { termName :: x }
  -- | We have a multi-tape grammar with a stack of just terminals. We
  -- normally can ignore the contents in the functions above, but keep them
  -- anyway.
  | StackedTerms { stackedTerms :: [ArgTy x] }
  -- | We have a multi-tape grammar, but the stack contains a mixture of
  -- @ArgTy@s.
  | StackedVars { stackedVars :: [ArgTy x] }
  -- | A single-dim @()@ case
  | NilVar
  -- | The result type name
  | Result { result :: x }
  deriving (Show,Eq)

unpackArgTy :: Show x => ArgTy x -> x
unpackArgTy = go
  where go (SynVar x) = x
        go (Term   x) = x
        go (Result x) = x
        go err        = error $ "unpackArgTy " ++ show err

-- | Get all synvars, even if deep in a stack

flattenSynVars :: ArgTy x -> [x]
flattenSynVars (SynVar x)       = [x]
flattenSynVars (StackedVars xs) = concatMap flattenSynVars xs
flattenSynVars _                = []

