# FusionSystems, ProtoEssentialChecks.gi, IsProtoEssential
#
gap> START_TEST("IsProtoEssential.tst");

gap> S := SmallGroup(64, 242);
<pc group of size 64 with 6 generators>
gap> M := MaximalSubgroups(S);;
gap> ForAny(M, A -> IsProtoEssential(S, A));
false
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsProtoEssential(S, A));;
gap> Length(C);
2
gap> ForAll(C, A -> Size(A) = 16 and IsElementaryAbelian(A));
true

gap> S := SmallGroup(256, 5352);
<pc group of size 256 with 8 generators>
gap> M := MaximalSubgroups(S);;
gap> M := Filtered(M, A -> IsProtoEssential(S, A));;
gap> Length(M);
1
gap> Centralizer(S, Omega(FS_SecondCentre(S), 2)) in M;
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsProtoEssential(S, A));;
gap> Length(C);
3
gap> Number(C, A -> IdGroup(A) = [64, 258]);
2

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> M := MaximalSubgroups(S);;
gap> M := Filtered(M, A -> IsProtoEssential(S, A));;
gap> Length(M);
2
gap> ForAll(M, A -> Exponent(A) = 3);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsProtoEssential(S, A));;
gap> Length(C);
3
gap> M[1] in C;
true
gap> M[2] in C;
true
gap> ForAny(C, A -> Size(A) = 3^2 and IsElementaryAbelian(A));
true

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsProtoEssential(S, A));;
gap> Length(C);
12
gap> ForAll(C, A -> Size(A) = 11^2);
true

gap> S := SmallGroup(5^5, 30);
<pc group of size 3125 with 5 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsProtoEssential(S, A));;
gap> Length(C);
11
gap> Number(C, A -> Size(A) = 25 and IsElementaryAbelian(A));
5
gap> Number(C, A -> Size(A) = 125 and IdGroup(A)[2] = 3);
5
gap> Number(C, A -> Size(A) = 5^4 and IsElementaryAbelian(A));
1

#
gap> STOP_TEST("IsProtoEssential.tst");
