0.4.1.0
-------

- initial support for multi-context free grammars
- mcfgs allow for interleaved syntactic variables
- applications include: natural language modelling and pseudoknotted structures in RNA
- the simplest formal language that requires this is: a^i b^j a^i b^j

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

