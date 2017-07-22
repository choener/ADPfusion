
# Implementors Notes (if you want to extend ADPfusion)



- The general inlining scheme is: (i) mkStream is {-# INLINE mkStream #-},
  inner functions like mk, step, worker functions, and index-modifying
  functions get an {-# INLINE [0] funName #-}. Where there is no function to
  annotate, use delay_inline.

- If you implement a new kind of memoizing table, like the dense Table.Array
  ones, you will have to implement mkStream code. When you hand to the left,
  the (i,j) indices and modify their extend (by, say, having NonEmpty table
  constaints), you have to delay_inline this (until inliner phase 0). Otherwise
  you will break fusion for mkStream.

- Terminals that capture both, say indexing functions, and data should have no
  strictness annotations for the indexing function. This allows the code to be
  duplicated, then inlined. This improves performance a lot, because otherwise
  a function is created that performs these lookups, which has serious (50%
  slower or so) performance implications.


# GHC Notes

## constructor specialization and worker wrapper limits

ADPfusion relies on extensive SpecCtor optimization. Starting (???) with GHC
8.2 compiler/specialise/SpecConstr.hs limits specialization to those functions,
where the number of worker-wrapper arguments is <= 10. For ADPfusion, one
should set -fmax-worker-args=100 or something similar -- at least in the
modules where the actual inlining happens and the real algorithm gets a {-#
NoInline costlyAlgo #-}.

## Demand analysis

Check CORE for demand analysis weirdness:
https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/Demand
