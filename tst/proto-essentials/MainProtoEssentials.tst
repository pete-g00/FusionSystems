# FusionSystems, ProtoEssentials.gi, MainProtoEssentials
#
gap> START_TEST("MainProtoEssentials.tst");

gap> S := SmallGroup(128, 931);
<pc group of size 128 with 7 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
5
gap> ForAll(C, A -> IsProtoEssential(S, A));
true
gap> Number(C, A -> IdGroup(A) = [ 64, 242 ]);
1
gap> Number(C, A -> IdGroup(A) = [ 64, 138 ]);
2
gap> Number(C, A -> IdGroup(A) = [ 32, 27 ]);
2
gap> C := MainProtoEssentials(S, 0);;
gap> Length(C);
3
gap> Number(C, A -> IdGroup(A) = [ 64, 242 ]);
1
gap> Number(C, A -> IdGroup(A) = [ 64, 138 ]);
0
gap> Number(C, A -> IdGroup(A) = [ 32, 27 ]);
2

gap> S := AbelianGroup([3,3,3]);
<pc group of size 27 with 3 generators>
gap> MainProtoEssentials(S);
[]
gap> MainProtoEssentials(S, 0);
[]
gap> MainProtoEssentials(S, -1);
[]

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
3
gap> ForAll(C, A -> IsProtoEssential(S, A));
true
gap> ForAny(C, A -> IdGroup(A) = [3^2, 2]);
true
gap> ForAny(C, A -> IdGroup(A) = [3^3, 5]);
true
gap> ForAny(C, A -> IdGroup(A) = [3^3, 3]);
true

gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
2
gap> IdGroup(C0[1]) = [3^2, 2];
true
gap> ForAny(C0, A -> IdGroup(A) = [3^2, 2]);
true
gap> ForAny(C0, A -> IdGroup(A) = [3^3, 5]);
true
gap> ForAny(C, A -> IsConjugate(S, A, C0[1]));
true
gap> ForAny(C, A -> IsConjugate(S, A, C0[2]));
true
gap> IsProtoEssential(S, C0[1]);
true
gap> IsProtoEssential(S, C0[2]);
true

gap> D := MainProtoEssentials(S, -1);;
gap> Length(D);
1
gap> IdGroup(D[1]) = [3^3, 3];
true
gap> IsProtoEssential(S, D[1]);
true
gap> ForAny(C, A -> IsConjugate(S, A, D[1]));
true

#
gap> STOP_TEST("MainProtoEssentials.tst");
