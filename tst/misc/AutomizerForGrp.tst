# FusionSystems, MISC.gi, AutomizerForGrp
#
gap> START_TEST("AutomizerForGrp.tst"); 

gap> S := TrivialGroup();
<pc group of size 1 with 0 generators>
gap> A := Automizer(S, S);;
gap> Size(A);
1

gap> S := AbelianGroup([3,3,3]);
<pc group of size 27 with 3 generators>
gap> A := Group(S.1, S.2);;
gap> Aut := AutomorphismGroup(S);;
gap> Size(Aut);
11232
gap> AutA := Automizer(Aut, A);;
gap> Size(AutA);
48

gap> S := SmallGroup(5^6, 636);
<pc group of size 15625 with 6 generators>
gap> x := ComplementClassesRepresentatives(S, Centralizer(S, FS_SecondCentre(S)))[1].1;;
gap> V := ClosureGroup(Center(S), x);;
gap> AutS := AutomorphismGroup(S);;
gap> AutV := AutomorphismGroup(V);;
gap> n := NiceMonomorphism(AutV);
<action isomorphism>
gap> AutV := n(AutV);;
gap> AutSV := Automizer(AutS, V);;
gap> AutSV := n(AutSV);;
gap> Size(AutSV);
20
gap> Index(AutV, AutSV);
24
gap> AutVp := NormalClosure(AutV, SylowSubgroup(AutV, 5));;
gap> IsSubset(AutVp, AutSV);
true

gap> S := SmallGroup(5^6, 644);
<pc group of size 15625 with 6 generators>
gap> x := ComplementClassesRepresentatives(S, Centralizer(S, FS_SecondCentre(S)))[1].1;;
gap> V := ClosureGroup(Center(S), x);;
gap> AutS := AutomorphismGroup(S);;
gap> AutV := AutomorphismGroup(V);;
gap> n := NiceMonomorphism(AutV);
<action isomorphism>
gap> AutV := n(AutV);;
gap> AutSV := Automizer(AutS, V);;
gap> AutSV := n(AutSV);;
gap> Size(AutSV);
20
gap> Index(AutV, AutSV);
24
gap> AutVp := NormalClosure(AutV, SylowSubgroup(AutV, 5));;
gap> IsSubset(AutVp, AutSV);
false

#
gap> STOP_TEST("AutomizerForGrp.tst", 1);
