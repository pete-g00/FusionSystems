# FusionSystems, MISC.gi, CentralizerMod
#
gap> START_TEST("CentralizerMod.tst"); 

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> L := LowerCentralSeries(S);
[ <pc group of size 81 with 4 generators>, Group([ f3, f4 ]), Group([ f4 ]), Group([ <identity> of ... ]) ]
gap> A := CentralizerMod(S, L[2], L[3]);
Group([ f1, f2, f3, f4 ])
gap> A := CentralizerMod(S, L[2], L[4]);
Group([ <identity> of ..., f2, f3, f4 ])
gap> A = Centralizer(S, FS_SecondCentre(S));
true

gap> S := SmallGroup(7^6, 807);
<pc group of size 117649 with 6 generators>
gap> L := LowerCentralSeries(S);
[ <pc group of size 117649 with 6 generators>, Group([ a3, a4, a5, a6 ]), Group([ a4, a5, a6 ]), Group([ a5, a6 ]), Group([ a6 ]),
  Group([ <identity> of ... ]) ]
gap> A := CentralizerMod(S, L[2], L[3]);
Group([ a1, a2, a3, a4, a5, a6 ])
gap> A := CentralizerMod(S, L[2], L[4]);
Group([ a1, <identity> of ..., a3, a4, a5, a6 ])
gap> A := CentralizerMod(S, L[3], L[5]);
Group([ a1, <identity> of ..., a3, a4, a5, a6 ])
gap> A = Centralizer(S, FS_SecondCentre(S));
false
gap> A := CentralizerMod(S, L[4], L[6]);
Group([ <identity> of ..., a2, a3, a4, a5, a6 ])
gap> A = Centralizer(S, FS_SecondCentre(S));
true

#
gap> STOP_TEST("CentralizerMod.tst", 1);
