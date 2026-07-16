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
gap> G := AlternatingGroup(9);
Alt( [ 1 .. 9 ] )
gap> S := SylowSubgroup(G,3);
Group([ (1,2,3), (4,5,6), (7,8,9), (1,4,7)(2,5,8)(3,6,9) ])
gap> AutGS := Automizer(G,S);
<group with 5 generators>
gap> BGS := SylowSubgroup(AutGS, 2);
<group of size 2 with 1 generator>
gap> M := MaximalSubgroups(S);;
gap> E1 := First(M, IsElementaryAbelian);
Group([ (1,2,3), (1,3,2)(4,5,6), (1,2,3)(4,5,6)(7,8,9) ])
gap> AutGE1 := Automizer(G, E1);
<group with 7 generators>
gap> BGE1 := SylowSubgroup(AutGE1, 2);
<group of size 8 with 3 generators>
gap> F := SaturatedFusionSystem(S, [BGE1.1, BGE1.2]);
<object>
gap> L := FClasses(F);;
gap> List(L, Size);
[ 1, 3, 6, 4, 9, 3, 6, 4, 3, 3, 3, 1, 1, 1, 1, 1 ]
gap> List(L, IsCentric);
[ false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true ]
gap> List(L, A -> IsSaturated(F,A));
[ true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true ]
gap> E2 := Group(S.1*S.2*S.3, S.4);
Group([ (1,2,3)(4,5,6)(7,8,9), (1,4,7)(2,5,8)(3,6,9) ])
gap> AutGE2 := Automizer(G, E2);
<group with 5 generators>
gap> BGE2 := SylowComplement(AutGE2, 3);
<group of size 8 with 3 generators>
gap> F := SaturatedFusionSystem(S, [BGE1.1, BGE1.2, BGE2.1, BGE2.2]);
<object>
gap> L := FClasses(F);;
gap> List(L, Size);
[ 1, 3, 6, 13, 3, 6, 4, 3, 3, 3, 1, 1, 1, 1, 1 ]
gap> List(L, IsCentric);
[ false, false, false, false, false, false, false, true, true, true, true, true, true, true, true ]
gap> List(L, A -> IsSaturated(F,A));
[ true, true, true, false, true, true, true, false, true, true, false, true, true, true, true ]
gap> F := SaturatedFusionSystem(S, [BGS.1, BGE2.1, BGE2.2]);
<object>
gap> L := FClasses(F);;
gap> List(L, Size);
[ 1, 3, 3, 3, 10, 3, 3, 3, 3, 3, 1, 3, 3, 3, 1, 1, 1, 1, 1 ]
gap> List(L, IsCentric);
[ false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true,
  true, true ]
gap> List(L, A -> IsSaturated(F,A));
[ true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true ]
gap> F := SaturatedFusionSystem(S, [BGS.1, BGE1.1, BGE1.2, BGE2.1, BGE2.2]);
<object>
gap> L := FClasses(F);;
gap> List(L, Size);
[ 1, 3, 6, 13, 3, 6, 4, 3, 3, 3, 1, 1, 1, 1, 1 ]
gap> List(L, IsCentric);
[ false, false, false, false, false, false, false, true, true, true, true, true, true, true, true ]
gap> List(L, A -> IsSaturated(F,A));
[ true, true, true, true, true, true, true, true, true, true, true, true, true, true, true ]
