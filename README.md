# The GAP package FusionSystems

The GAP package `FusionSystems` is a package that allows us to work with fusion systems in GAP. It is currently a work in progress and supports the construction of proto-essential subgroups. We also currently support (a non-exhaustive) check as to whether a group can support corefree and reduced fusion systems. 

The first version of the package aims to add further functionalities, including (but not limited to):
* constructing fusion systems in GAP;
* storing small fusion systems; and
* checking a fusion system is saturated.

## Installation
1. Go to the `pkg` directory inside your gap folder. 
2. Run the following command -- `git clone https://github.com/pete-g00/FusionSystems`
3. Launch GAP, and load the package `fusionsystems`. If the package has been loaded correctly, it will print the following:

``` 
     ● G  GAP 4.16.0 of 2026-06-02
  ● ●  A  https://www.gap-system.org
     ● P  Architecture: x86_64-pc-linux-gnu-default64-kv11
 Configuration:  gmp 6.3.0, GASMAN, readline
 Loading the library and packages ...
 Packages:   AClib 1.3.3, Alnuth 4.0.0, AtlasRep 2.1.11, AutoDoc 2026.05.11, AutPGrp 1.12.0, Browse 1.8.22, CRISP 1.4.8,
             Cryst 4.1.31, CrystCat 1.1.11, CTblLib 1.3.11, FactInt 1.6.3, FGA 1.5.0, Forms 1.3.0, GAPDoc 1.6.10, genss 1.6.9,
             IO 4.9.3, IRREDSOL 1.4.4, LAGUNA 3.9.7, orb 5.1.0, PackageManager 1.6.3, Polenta 1.3.11, Polycyclic 2.18,
             PrimGrp 4.0.2, RadiRoot 2.9, recog 1.5.1, ResClasses 4.7.4, SmallGrp 1.5.4, Sophus 1.27, SpinSym 1.5.2,
             StandardFF 1.0, TomLib 1.2.11, TransGrp 3.6.5, utils 0.95
 Try '??help' for help. See also '?copyright', '?cite' and '?authors'
gap> LoadPackage("fusionsystems");
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
Loading ANUPQ 3.3.3 (ANU p-Quotient)
by Greg Gamble (GAP code, Greg.Gamble@uwa.edu.au),
   Werner Nickel (GAP code), and
   Eamonn O'Brien (C code, https://www.math.auckland.ac.nz/~obrien).
maintained by:
   Max Horn (https://www.quendi.de/math).
uses ANU pq binary (C code program) version: 1.9
Homepage: https://gap-packages.github.io/anupq/
Report issues at https://github.com/gap-packages/anupq/issues
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
Loading FORMAT 1.4.5 (Formations of Finite Soluble Groups)
by Bettina Eick (http://www.iaa.tu-bs.de/beick) and
   Charles R.B. Wright (https://pages.uoregon.edu/wright/).
maintained by:
   Bettina Eick (http://www.iaa.tu-bs.de/beick) and
   The GAP Team (support@gap-system.org).
Homepage: https://gap-packages.github.io/format/
Report issues at https://github.com/gap-packages/format/issues
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
Loading FusionSystems 0.1 (A GAP package on fusion systems)
by Pete Gautam (https://github.com/pete-g00) and
   Justin Lynd (https://userweb.ucs.louisiana.edu/~jxl7583/).
maintained by:
   Pete Gautam (https://github.com/pete-g00).
Homepage: https://pete-g00.github.io/FusionSystems
Report issues at https://pete-g00.github.io/FusionSystems/issues
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
true
```

## Authors
The current version of the package was mainly created by:

1. Pete Gautam, University of Manchester
1. Justin Lynd, University of Louisiana

We further acknowledge contributions from Josh Bridges and David Burrell.

## Contact

If you have any questions, suggestions, please start an issue or create a PR in the repository. You can also contact Pete Gautam <pratyush.gautam@manchester.ac.uk>.
