0.3.0.0
-------

- simplified boundary checking: sometimes gives performance gain (!) due to one
  loop variable less
- optimized loop variable design following "The HERMIT in the Stream" (Farmer
  et al, 2014)
- somewhat nicer programmer interfaces
- less type classes to worry about
- there should be no loss of performance
- automatic filling and freezing of tables
- multiple example algorithms (build with -fexamples switch):
  - Needleman-Wunsch global alignment
  - RNA secondary structure prediction using simple base pair maximization

0.2.x.x
-------

- Streamlined interface: access everything via ADP.Fusion
- /Multi-tape/ grammars can now be written and are fused

