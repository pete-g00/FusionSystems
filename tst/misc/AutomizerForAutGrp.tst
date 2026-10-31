# FusionSystems, MISC.gi, AutomizerForAutGrp
#
gap> START_TEST("AutomizerForAutGrp.tst"); 

gap> S := TrivialGroup();
<pc group of size 1 with 0 generators>
gap> AutS := AutomorphismGroup(S);;
gap> A := Automizer(AutS, S);;
gap> Size(A);
1

gap> G := AlternatingGroup(9);
Alt( [ 1 .. 9 ] )
gap> S := SylowSubgroup(G, 3);
Group([ (1,2,3), (4,5,6), (7,8,9), (1,4,7)(2,5,8)(3,6,9) ])
gap> AutGS := Automizer(G, S);;
gap> Size(AutGS);
54
gap> M := MaximalSubgroups(S);;
gap> AutGM := List(M, A -> Automizer(G, A));;
gap> i := PositionProperty(M, A -> IdGroup(A) = [3^3, 3]);;
gap> Size(AutGM[i]);
54
gap> i := PositionProperty(M, A -> IdGroup(A) = [3^3, 4]);;
gap> Size(AutGM[i]);
54
gap> i := PositionProperty(M, A -> IdGroup(A) = [3^3, 5]);;
gap> A := M[i];;
gap> Size(AutGM[i]);
24
gap> C := SubgroupsSolvableGroup(S);;
gap> AutGC := List(C, A -> Automizer(G, A));;
gap> i := PositionProperty(C, A -> Size(A) = 3^2 and Centralizer(S,A) = A);;
gap> V := C[i];;
gap> Size(AutGC[i]);
24
gap> ForAll([1..Length(C)], i -> Centralizer(S,C[i]) <> Center(C[i]) or 
>   (C[i] in [S, A, V] or Size(PCore(AutGC[i], 3)) <> Index(C[i], Center(C[i]))));
true

#
gap> STOP_TEST("AutomizerForAutGrp.tst", 1);
