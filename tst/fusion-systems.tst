gap> S := DihedralGroup(8);
<pc group of size 8 with 3 generators>
gap> M := MaximalSubgroups(S);;
gap> M := Filtered(M, IsElementaryAbelian);
[ Group([ f1, f3 ]), Group([ f1*f2, f3 ]) ]
gap> E1 := M[1];
Group([ f1, f3 ])
gap> E2 := M[2];
Group([ f1*f2, f3 ])
gap> A := AutomorphismGroup(E1);
<group with 4 generators>
gap> x := SylowSubgroup(A,3);
<group>
gap> GeneratorsOfGroup(x);
[ [ f1, f3 ] -> [ f1*f3, f1 ] ]
gap> x1 := x.1;
[ f1, f3 ] -> [ f1*f3, f1 ]
gap> A := AutomorphismGroup(E2);
<group with 4 generators>
gap> x := SylowSubgroup(A,3);
<group>
gap> GeneratorsOfGroup(x);
[ [ f1*f2, f3 ] -> [ f1*f2*f3, f1*f2 ] ]
gap> x2 := x.1;
[ f1*f2, f3 ] -> [ f1*f2*f3, f1*f2 ]
gap> F := SaturatedFusionSystem(S, [x1,x2]);
<object>
gap> IsFusionSystem(F);
true
gap> L := FClasses(F);;
gap> Length(L);
6
gap> List(L, Size);
[ 1, 5, 1, 1, 1, 1 ]
gap> Sum(List(L, Size));
10
gap> List(L, C -> IsSaturated(F, C));
[ true, true, true, true, true, true ]
