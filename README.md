![github action: master](https://github.com/choener/ADPfusion/actions/workflows/action.yml/badge.svg)

# ADPfusion

[*generalized Algebraic Dynamic Programming Homepage*](http://www.bioinf.uni-leipzig.de/Software/gADP/)

Ideas implemented here are described in a couple of papers:



1.  Christian Hoener zu Siederdissen  
    *Sneaking Around ConcatMap: Efficient Combinators for Dynamic Programming*  
    2012, Proceedings of the 17th ACM SIGPLAN international conference on Functional programming  
    [paper](http://doi.acm.org/10.1145/2364527.2364559) [preprint](http://www.tbi.univie.ac.at/newpapers/pdfs/TBI-p-2012-2.pdf)  
1.  Andrew Farmer, Christian Höner zu Siederdissen, and Andy Gill.  
    *The HERMIT in the stream: fusing stream fusion’s concatMap*  
    2014, Proceedings of the ACM SIGPLAN 2014 workshop on Partial evaluation and program manipulation.  
    [paper](http://dl.acm.org/citation.cfm?doid=2543728.2543736)  
1.  Christian Höner zu Siederdissen, Ivo L. Hofacker, and Peter F. Stadler.  
    *Product Grammars for Alignment and Folding*  
    2014, IEEE/ACM Transactions on Computational Biology and Bioinformatics. 99  
    [paper](http://ieeexplore.ieee.org/xpl/articleDetails.jsp?arnumber=6819790)  
1.  Christian Höner zu Siederdissen, Sonja J. Prohaska, and Peter F. Stadler  
    *Algebraic Dynamic Programming over General Data Structures*  
    2015, BMC Bioinformatics  
    [preprint](http://www.bioinf.uni-leipzig.de/Software/gADP/preprints/hoe-pro-2015.pdf)  
1.  Maik Riechert, Christian Höner zu Siederdissen, and Peter F. Stadler  
    *Algebraic dynamic programming for multiple context-free languages*  
    2016, Theoretical Computer Science  
    [preprint](http://www.bioinf.uni-leipzig.de/Software/gADP/preprints/rie-hoe-2015.pdf)  



# Introduction

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




# Installation

Follow the [gADP examples](http://www.bioinf.uni-leipzig.de/Software/gADP/index.html).



# Implementors Notes (if you want to extend ADPfusion)

These have been moved to [HACKING.md](https://github.com/choener/ADPfusion/blob/master/HACKING.md).

#### Contact

Christian Hoener zu Siederdissen  
Leipzig University, Leipzig, Germany  
choener@bioinf.uni-leipzig.de  
<http://www.bioinf.uni-leipzig.de/~choener/>  

