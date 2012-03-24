
ADPfusion
(c) 2012, Christian Hoener zu Siederdissen
University of Vienna, Vienna, Austria
choener@tbi.univie.ac.at
LICENSE: BSD3



Introduction
============

ADPfusion combines stream-fusion (using the stream interface provided by the
vector library) and type-level programming to provide highly efficient dynamic
programming combinators.

From the programmers' viewpoint, ADPfusion behaves very much like the original
ADP implementation <http://bibiserv.techfak.uni-bielefeld.de/adp/> developed by
Robert Giegerich and colleagues, though both combinator semantics and
backtracking are different.

The library internals, however, are designed not only to speed up ADP by a
large margin (which this library does), but also to provide further runtime
improvements by allowing the programmer to switch over to other kinds of data
structures with better time and space behaviour. Most importantly, dynamic
programming tables can be strict, removing indirections present in lazy, boxed
tables.

As an example, even rather complex ADP code tends to be completely optimized to
loops that use only unboxed variables (Int# and others, indexIntArray# and
others).

Completely novel (compared to ADP), is the idea of allowing efficient monadic
combinators. This facilitates writing code that performs backtracking, or
samples structures stochastically, among others things.

This version is still highly experimental and makes use of multiple recent
improvements in GHC. This is particularly true for the monadic interface.

Long term goals: Outer indices with more than two dimensions, specialized table
design, a combinator library, a library for computational biology.

If possible, build using the GHC llvm backend, and GHC-7.2.2.  GHC-7.4.x
produces very bad code on my system, please benchmark using 7.2.2.

Two algorithms from the realm of computational biology are provided as examples
on how to write dynamic programming algorithms using this library:
<http://hackage.haskell.org/package/Nussinov78> and
<http://hackage.haskell.org/package/RNAfold>.


Installation
============

Please use GHC-7.2.2, if possible. GHC-7.4 currently seems to have problems
optimizing vector-dependent code:
http://hackage.haskell.org/trac/ghc/ticket/5539
(and others?)

If GHC-7.2.2, LLVM and cabal-install are available, you should be all set. I
recommend using cabal-dev as it provides a very nice sandbox (replace cabal-dev
with cabal otherwise).

If you go with cabal-dev, no explicit installation is necessary and ADPfusion
will be installed in the sandbox together with the example algorithms or your
own.

For a more global installation, "cabal install ADPfusion" should do the trick.

To run the Quickcheck tests, do an additional "cabal-dev install QuickCheck",
then "cabal-dev ghci", ":l ADP/Fusion/QuickCheck.hs", and "allProps". Loading
the quickcheck module should take a bit due to compilation. "allProps" tests
all properties and should yield no errors.



Notes
=====

If you have problems, find bugs, or want to use this library to write your own
DP algorithms, please send me a mail. I'm very interested in hearing what is
missing.

One of the things I'll be integrating is an extension to higher dimensions
(more than two).

Right now, I am not quite happy with the construction and destruction of the
"Box" representations. These will change soon. In addition, an analysis of the
actual combinators should remove the need for nested applications of objective
functions in many cases.



VERSION HISTORY
===============

- 0.0.0.3:
  - initial version, together with submitted paper

- 0.0.0.4:
  - based most combinators on just two generalized Box creators
  - cleaned up and simplified RNAfold example
  - RNAfold execution now a bit slower. Simplified energy functions typically
    only have three arguments now, which can be of 'Primary' type. While this
    reduces speed because we will repeatedly ask for the same value, it is much
    easier to handle the different functions and ``play'' with fusion
    properties.
  - RNAfold compilation massively faster: execution/compilation tradoff is
    worth it for experimenting with ADPfusion; still faster than anything
    except RNAfold itself. We are now now 2.8x times slower, but 3.5x times
    slower
  - Quickcheck properties for many combinators
  - Unit tests for RNAfold functions
  - will soon split off RNAfold and Nussinov and publish three hackage
    libraries
  - this version was never available, after being done, a split into library
    and examples was performed.

- 0.0.1.0
  - providing just the library. Examples are found in different libraries.

