
module ADPfusion.Core.SynVar.Fill where

import           Control.Monad
import           Control.Monad.Morph (hoist, MFunctor (..))
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Control.Monad.Trans.Class (lift, MonadTrans (..))
import           Control.Monad (when,forM_)
import           Data.Dynamic
import           Data.List (nub,sort,group)
import           Data.Maybe (fromJust)
import           Data.Proxy
import           Data.Type.Equality
import           Data.Vector.Fusion.Util (Id(..))
import           Debug.Trace (traceShow)
import           GHC.Exts (inline)
import           GHC.TypeNats
import qualified Data.Data as D
import qualified Data.List as L
import qualified Data.Typeable as T
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Unboxed as VU
import qualified GHC.Generics as G
import           System.IO.Unsafe
import           System.CPUTime
import           GHC.Conc (pseq)

import           Data.PrimitiveArray

import           ADPfusion.Core.SynVar.Array -- TODO we want to keep only classes in here, move instances to the corresponding modules
import           ADPfusion.Core.SynVar.Recursive.Type
import           ADPfusion.Core.SynVar.TableWrap

import           Debug.Trace



{-

-- | A vanilla context-free grammar

data CFG

-- | This grammar is a multi-cfg in a monotone setting

data MonotoneMCFG


-- * Unsafely mutate 'ITbls' and similar tables in the forward phase.

-- | Mutate a cell in a stack of syntactic variables.
--
-- TODO generalize to monad morphism via @mmorph@ package. This will allow
-- more interesting @mrph@ functions that can, for example, track some
-- state in the forward phase. (Note that this can be dangerous, we do
-- /not/ want to have this state influence forward results, unless that can
-- be made deterministic, or we'll break Bellman)

class MutateCell (h ∷ *) (s ∷ *) (im ∷ * → *) i where
  mutateCell
    ∷ (Monad om, PrimMonad om)
    ⇒ Proxy h
    → Int
    → Int
    → (forall a . im a → om a)
    → s
    → LimitType i
    → i
    → om ()

-- |

class MutateTables (h :: *) (s :: *) (im :: * -> *) where
  mutateTables :: (Monad om, PrimMonad om) => Proxy h -> (forall a . im a -> om a) -> s -> om s

class TableOrder (s :: *) where
  tableLittleOrder :: s -> [Int]
  tableBigOrder :: s -> [Int]

instance TableOrder Z where
  tableLittleOrder Z = []
  tableBigOrder Z = []
  {-# Inline tableLittleOrder #-}
  {-# Inline tableBigOrder #-}

instance
  ( TableOrder ts
  , KnownNat bo
--  , KnownNat lo
  ) ⇒ TableOrder (ts:.TwITbl bo im arr c i x) where
  tableLittleOrder (ts:.TW (ITbl tlo _ _) _) =
    let -- tlo = fromIntegral $ natVal (Proxy ∷ Proxy lo)
    in  tlo : tableLittleOrder ts
  tableBigOrder    (ts:.TW (ITbl _ _ _) _) =
    let tbo = fromIntegral $ natVal (Proxy ∷ Proxy bo)
    in  tbo : tableBigOrder ts
  {-# Inline tableLittleOrder #-}
  {-# Inline tableBigOrder #-}

-- | @IRec@s do not need an order, given that they do not memoize.

instance (TableOrder ts) => TableOrder (ts:.TwIRec im c i x) where
  tableLittleOrder (ts:._) = tableLittleOrder ts
  tableBigOrder    (ts:._) = tableBigOrder ts
  {-# Inline tableLittleOrder #-}
  {-# Inline tableBigOrder #-}

-- ** individual instances for filling a *single cell*

instance
  (
  ) => MutateCell p Z im i where
  mutateCell _ _ _ _ Z _ _ = return ()
  {-# INLINE mutateCell #-}

instance
  ( MutateCell CFG ts im i
  ) => MutateCell CFG (ts:.TwIRec im c i x) im i where
  mutateCell h bo lo mrph (ts:._) lu i = do
    mutateCell h bo lo mrph ts lu i
  {-# Inline mutateCell #-}

instance
  ( PrimArrayOps  arr i x
  , MPrimArrayOps arr i x
  , MutateCell CFG ts im i
  , KnownNat bo
--  , KnownNat lo
  ) => MutateCell CFG (ts:.TwITbl bo im arr c i x) im i where
  mutateCell h bo lo mrph (ts:.TW (ITbl tlo c arr) f) lu i = do
    let tbo = fromIntegral $ natVal (Proxy ∷ Proxy bo)
--        tlo = fromIntegral $ natVal (Proxy ∷ Proxy lo)
    mutateCell h bo lo mrph ts lu i
    when (bo==tbo && lo==tlo) $ do
      marr <- unsafeThaw arr
      z <- (inline mrph) $ f lu i
      writeM marr i z
  {-# INLINE mutateCell #-}

{-
 - TODOThe following code goes into ADPfusionSubword!
 -
type ZS2 = Z:.Subword I:.Subword I

instance
  ( PrimArrayOps  arr ZS2 x
  , MPrimArrayOps arr ZS2 x
  , MutateCell MonotoneMCFG ts im ZS2
  ) => MutateCell MonotoneMCFG (ts:.TwITbl im arr c ZS2 x) im ZS2 where
  mutateCell h bo lo mrph (ts:.TW (ITbl tbo tlo c arr) f) lu iklj@(Z:.Subword (i:.k):.Subword(l:.j)) = do
    mutateCell h bo lo mrph ts lu iklj
    when (bo==tbo && lo==tlo && k<=l) $ do
      marr <- unsafeThaw arr
      z <- (inline mrph) $ f lu iklj
      writeM marr iklj z
  {-# INLINE mutateCell #-}

instance
  ( PrimArrayOps arr (Subword I) x
  , MPrimArrayOps arr (Subword I) x
  , MutateCell h ts im (Z:.Subword I:.Subword I)
  ) => MutateCell h (ts:.TwITbl im arr c (Subword I) x) im (Z:.Subword I:.Subword I) where
  mutateCell h bo lo mrph (ts:.TW (ITbl tbo tlo c arr) f) lu@(Z:.Subword (l:._):.Subword(_:.u)) ix@(Z:.Subword (i1:.j1):.Subword (i2:.j2)) = do
    mutateCell h bo lo mrph ts lu ix
    when (bo==tbo && lo==tlo && i1==i2 && j1==j2) $ do
      let i = i1
      let j = j1
      marr <- unsafeThaw arr
      z <- (inline mrph) $ f (subword l u) (subword i j)
      writeM marr (subword i j) z
  {-# Inline mutateCell #-}
-}


-- ** individual instances for filling a complete table and extracting the
-- bounds

instance
  ( MutateCell h (ts:.TwITbl bo im arr c i x) im i
  , PrimArrayOps arr i x
  , Show i
  , IndexStream i
  , TableOrder (ts:.TwITbl bo im arr c i x)
  ) => MutateTables h (ts:.TwITbl bo im arr c i x) im where
  mutateTables h mrph tt@(_:.TW (ITbl lo _ arr) _) = do
    let to = upperBound arr
    -- TODO (1) find the set of orders for the synvars
    let !tbos = VU.fromList . nub . sort $ tableBigOrder tt
    let !tlos = VU.fromList . nub . sort $ tableLittleOrder tt
    VU.forM_ tbos $ \bo ->
      case (VU.length tlos) of
        1 -> let lo = VU.head tlos
             in  flip SM.mapM_ (streamUp zeroBound' to) $ \k ->
                  mutateCell h bo lo (inline mrph) tt to k
        -- TODO each big-order group should be allowed to have its own sets
        -- of bounds. within a group, it doesn't make a lot of sense to
        -- have different bounds? Is there a use case for that even?
        _ -> flip SM.mapM_ (streamUp zeroBound' to) $ \k ->
              VU.forM_ tlos $ \lo ->
                mutateCell h bo lo (inline mrph) tt to k
    return tt
  {-# INLINE mutateTables #-}

-- | Default table filling, assuming that the forward monad is just @IO@.
--
-- TODO generalize to @MonadIO@ or @MonadPrim@.

mutateTablesDefault :: MutateTables CFG t Id => t -> t
mutateTablesDefault t = unsafePerformIO $ mutateTables (Proxy :: Proxy CFG) (return . unId) t
{-# INLINE mutateTablesDefault #-}

-- | Mutate tables, but observe certain hints. We use this for monotone
-- mcfgs for now.

mutateTablesWithHints :: MutateTables h t Id => Proxy h -> t -> t
mutateTablesWithHints h t = unsafePerformIO $ mutateTables h (return . unId) t






mutateTablesST t = runST $ mutateTablesNew t
{-# Inline mutateTablesST #-}

class CountNumberOfCells t where
  countNumberOfCells ∷ t → Integer

instance CountNumberOfCells Z where
  countNumberOfCells Z = 0

instance
  ( CountNumberOfCells ts
  , Index i
  , PrimArrayOps arr i x
  ) ⇒ CountNumberOfCells (ts:.TwITbl bo Id arr c i x) where
  countNumberOfCells (ts:.(TW (ITbl lo _ arr) fun)) =
    countNumberOfCells ts + (product . totalSize $ upperBound arr)

data PerfCounter = PerfCounter
  { picoSeconds   :: !Integer
  , seconds       :: !Double
  , numberOfCells :: !Integer
  }
  deriving (Eq,Ord,Show)

data Mutated ts = Mutated
  { mutatedTables ∷ !ts
  , perfCounter   ∷ !PerfCounter
  , eachBigPerfCounter  ∷ [PerfCounter]
  }

-- | 
--
-- TODO new way how to do table filling. Because we now have heterogeneous
-- tables (i) group tables by @big order@ into different bins; (ii) check
-- that each bin has the same bounds (needed? -- could we have
-- smaller-sized tables once in a while); (iii) run each bin one after the
-- other
--
-- TODO measure performance penalty, if any. We might need liberal
-- INLINEABLE, and specialization. On the other hand, we can do the
-- freeze/unfreeze outside of table filling.

mutateTablesNew
  :: forall t m .
     ( TableOrder t
     , TSBO t
     , Monad m
     , PrimMonad m
     , CountNumberOfCells t
     )
  => t
  -> m (Mutated t)
mutateTablesNew ts = do
  -- sort the tables according to [bigorder,type,littleorder]. For each
  -- @bigorder@, we should have only one @type@ and can therefor do the
  -- following (i) get subset of the @ts@, (ii) use outermost of @ts@ to
  -- get bounds, (iii) fill these tables
  -- let !tbos = VU.fromList . nub . sort $ tableBigOrder ts
  let justOrder = L.map (\d → (qBigOrder d, qLittleOrder d))
  let ds = L.sort $ asDyn ts
  let goM ∷ (Monad m, PrimMonad m) ⇒ [Q] → [PerfCounter] → m [PerfCounter]
      goM [] ps = return $ reverse ps
      goM xs ps = do
        (ys,p) <- fillWithDyn xs ts
        goM ys (p:ps)
      {-# Inlinable goM #-}
  startTime ← unsafeIOToPrim getCPUTime
  ps ← goM ds []
  stopTime  ← unsafeIOToPrim getCPUTime
  let deltaTime = max 1 $ stopTime - startTime
  return $! Mutated
    { mutatedTables = ts
    , perfCounter   = PerfCounter
        { picoSeconds   = deltaTime
        , seconds       = 1e-12 * fromIntegral deltaTime
        , numberOfCells = countNumberOfCells ts
        }
    , eachBigPerfCounter = ps
    }
{-# Inline mutateTablesNew #-}

data Q = Q
  { qBigOrder     :: Int
  , qLittleOrder  :: Int
  , qTypeRep      :: T.TypeRep
  , qObject       :: Dynamic
  , qTable        :: Dynamic
  , qFunction     :: Dynamic
  }
  deriving (Show)

instance Eq Q where
  Q bo1 lo1 tr1 _ _ _ == Q bo2 lo2 tr2 _ _ _ = (bo1,tr1,lo1) == (bo2,tr2,lo2)

instance Ord Q where
  Q bo1 lo1 tr1 _ _ _ `compare` Q bo2 lo2 tr2 _ _ _ = (bo1,lo1,tr1) `compare` (bo2,lo2,tr2)

-- | Find the outermost table that has a certain big order and then fill
-- from there.

class TSBO t where
  asDyn :: t -> [Q]
  fillWithDyn :: (Monad m, PrimMonad m) => [Q] -> t -> m ([Q], PerfCounter)

instance TSBO Z where
  asDyn Z = []
  fillWithDyn qs Z = return (qs, PerfCounter 0 0 0)
  {-# Inlinable asDyn #-}
  {-# Inline fillWithDyn #-}

instance
 ( TSBO ts
 , Typeable arr
 , Typeable c
 , Typeable i
 , Typeable x
 , PrimArrayOps arr i x
 , MPrimArrayOps arr i x
 , IndexStream i
 , KnownNat bo
-- , KnownNat lo
 ) => TSBO (ts:.TwITbl bo Id arr c i x) where
  asDyn (ts:.t@(TW (ITbl lo _ arr) fun)) =
    let bo = fromIntegral $ natVal (Proxy ∷ Proxy bo)
--        lo = fromIntegral $ natVal (Proxy ∷ Proxy lo)
    in  Q bo lo (T.typeOf t) (toDyn t) (toDyn arr) (seq fun $ toDyn fun) : asDyn ts
  fillWithDyn qs (ts:.t@(TW (ITbl _ _ arrDirect) fDirect)) = do
    let to = upperBound arrDirect
        bo = fromIntegral $ natVal (Proxy ∷ Proxy bo)
--        lo = fromIntegral $ natVal (Proxy ∷ Proxy lo)
    -- @hs@ are all tables that can be filled here
    -- @ns@ are all tables we can't fill and need to process further down
    -- the line
    -- TODO FIXME FIXME FIXME why are the typereps different???
    let (hs,ns) = L.span (\Q{..} -> qBigOrder == bo) qs -- && qTypeRep == T.typeOf t) qs
    if null hs
      then fillWithDyn qs ts
      else do
        let ms = Prelude.map concreteTW hs
            af = Prelude.map concreteAF hs
            concreteTW  = (maybe (error "fromDynamic should not fail!")
                           (\x -> x `asTypeOf` t)
                          . fromDynamic . qObject)
            concreteAF q  = ( (`asTypeOf` arrDirect) . fromJust . fromDynamic $ qTable    q
                            , (`asTypeOf` fDirect)   . fromJust . fromDynamic $ qFunction q
                            )
        -- We have a single table and should short-circuit here
        --
        -- TODO we should specialize for tables of lengh @1..k@ for some
        -- small k. For @1@ and Needleman-Wunsch, we have a very nice @1.8@
        -- seconds down to @1.25@ seconds. :-)
        --
        -- TODO how about
        -- case ms of
        --   [a] -> bla
        --   [a,b] -> bla
        --   [a,b,c] -> bla
        --   [a:b:c:d:ms'] -> bla >> go ms'
        --   measure if this yields meaningful performance improvements
        --
        -- TODO also consider if we maybe just put marrfs into a vector
        --
        -- TODO we should use TH here.
        --
        -- (1) Have @Proxy @0@, say to set up big and small orders -- this
        -- gives us the order on the type level. @data One = One, data Two
        -- = Two, ...@ might be easier... maybe this is not too annoying to
        -- write using type equality
        -- 
        -- (2) Then deconstruct the @ts:.t@ things with TH into the correct
        -- pieces.
        --
        -- (3) Finally generate fill code. This should yield to performance
        -- similar to what we have here with the @case of 1@ construction,
        -- because @fDirect@ is partially floated out.
        --
        marrfs <- V.fromList <$> Prelude.mapM (\(TW (ITbl _ _ arr) f) -> unsafeThaw arr >>= \marr -> return (marr,f)) ms
        startTime ← unsafeIOToPrim getCPUTime
        case (V.length marrfs) of
          1 -> do -- let (!marr,!f) = marrfs V.! 0   -- this takes 1.3 seconds for NeedlemanWunsch
                  -- marr <- unsafeThaw arrDirect  -- this takes 0.8 seconds for NeedlemanWunsch
                  marr <- unsafeThaw arrDirect -- (fst $ af!!0)  -- this takes 1.3 seconds for NeedlemanWunsch
                  let !ffff = fDirect --snd $ af!!0
                  flip SM.mapM_ (streamUp zeroBound' to) $ \k -> do
                    -- TODO @inline mrph@ ...
                    z <- (return . unId) $ fDirect to k
                    writeM marr k z
        -- We have more than one table in will work over the list of tables
          _ -> do flip SM.mapM_ (streamUp zeroBound' to) $ \k ->
                    V.forM_ marrfs $ \(marr,f) -> do
                      z <- (return . unId) $ f to k
                      writeM marr k z
        -- traceShow (hs,length ms) $
        stopTime ← unsafeIOToPrim getCPUTime
        let deltaTime = stopTime - startTime
        let perf = PerfCounter
              { picoSeconds   = deltaTime
              , seconds       = 1e-12 * fromIntegral deltaTime
              , numberOfCells = sum $ Prelude.map (\(TW t _) → product . totalSize . upperBound $ iTblArray t) ms
              }
        return (ns, perf)
  {-# Inline fillWithDyn #-}

-- We don't need to capture @IRec@ tables as no table-filling takes place
-- for those tables. @asDyn@ therefore just collects on the remaining @ts@,
-- while @fillWithDyn@ hands of to the next possible table.

instance
  ( TSBO ts
  ) => TSBO (ts:.TwIRec Id c i x) where
  asDyn (ts:.t@(TW (IRec _ _) _)) = asDyn ts
  fillWithDyn qs (ts:._) = fillWithDyn qs ts
  {-# Inlinable asDyn #-}
  {-# Inline fillWithDyn #-}

-}

