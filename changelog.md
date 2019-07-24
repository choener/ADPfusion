0.6.0.0
-------

- major change as to how rule compilation proceeds (ctor spec -> type class instances)
- use new PrimitiveArray-0.9.0.0
- backtrace from any given index using 'axiomAt'
- Epsilon is tagged @Global or @Local, to allow local-alignment style algorithms

0.5.3.0
-------

- using unboxed Ints (primbool style) for rule guards. This nets a nice speedup
  of 30-50% for linear languages

0.5.2.2
-------

- Modified signature of Edge to make explicit the @From@ and @To@ nodes of the
  edge. Minor version bump, because @Edge@ is not official yet.
- optimized table filling yields large improvements for linear languages

0.5.2.1
-------

- removed upper bounds

0.5.2.0
-------

- table filling fully inlined in the forward algorithm
- experimental PrimBool operations
- note: these optimizations are mostly of interest for linear languages, where
  is rule (or function call) is comparatively expensive
- major re-arrangement of modules: import ADP.Fusion.Core for development of
  novel DP systems. Import ADP.Fusion.Point if you want to write a sequence
  alignment algorithm

0.5.1.0
-------

- improved table filling algorithm performance
- some optimizations to terminal symbols

0.5.0.0
-------

- complete re-design of Inside / Outside / Complement handling based on phantom
  types
- very liberal combination of multi-tape grammars
- simplified index generation system (both faster, and easier to write new
  symbol now)

0.4.1.1
-------

- bugfix in Multitape Subword Index calculations (A.F.S.Indices.hs) [this one
  is quite spurious. I needed quickcheck to find a suitable minimal example
  where Pseudoknot.hs fails]

0.4.1.0
-------

- initial support for multi-context free grammars
- mcfgs allow for interleaved syntactic variables
- applications include: natural language modelling and pseudoknotted structures
  in RNA
- the simplest formal language that requires this is: a^i b^j a^i b^j
- the [GenussFold](http://hackage.haskell.org/package/GenussFold) library gives
  a simple example grammar

0.4.0.2
-------

- bugfixes

0.4.0.0
-------

- travic-ci integration
- forward phase now operates on immutable tables that are internally thawed
- resembles the behavior of Data.Vector.Generic.constructN
- Empty needs to be bound to input. We require this as certain index structures
  have no natural notion of and empty index -- unless one provides additional
  information in the index

0.3.0.0
-------

- simplified boundary checking: sometimes gives performance gain (!) due to one
  loop variable less
- optimized loop variable design following "The HERMIT in the Stream" (Farmer
  et al, 2014)
- somewhat nicer programmer interfaces
- automatic filling and freezing of tables
- multiple example algorithms (build with -fexamples switch):
  - Needleman-Wunsch global alignment
  - RNA secondary structure prediction using simple base pair maximization
- updated Table code to handle single-dim Subwords in a better way.
- simplified backtracking

0.2.x.x
-------

- Streamlined interface: access everything via ADP.Fusion
- /Multi-tape/ grammars can now be written and are fused

