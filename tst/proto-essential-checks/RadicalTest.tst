# FusionSystems, ProtoEssentialChecks.gi, RadicalTest
#
gap> START_TEST("RadicalTest.tst");

gap> S := SmallGroup(64, 242);
<pc group of size 64 with 6 generators>
gap> M := MaximalSubgroups(S);;
gap> Number(M, A -> RadicalTest(S, A));
0
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Centralizer(S, A) = Center(A));;
gap> C := Filtered(C, A -> RadicalTest(S, A));;
gap> Length(C);
3
gap> ForAll(C, A -> A = S or (Size(A) = 16 and IsElementaryAbelian(A)));
true

gap> S := SmallGroup(256, 5352);
<pc group of size 256 with 8 generators>
gap> M := MaximalSubgroups(S);;
gap> Number(M, A -> RadicalTest(S, A));
1
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Centralizer(S, A) = Center(A));;
gap> C := Filtered(C, A -> RadicalTest(S, A));;
gap> Length(C);
8
gap> Number(C, A -> IdGroup(A) = [64, 258]);
2

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> M := MaximalSubgroups(S);;
gap> M := Filtered(M, A -> RadicalTest(S, A));;
gap> Length(M);
2
gap> ForAll(M, A -> Exponent(A) = 3);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Centralizer(S, A) = Center(A));;
gap> C := Filtered(C, A -> RadicalTest(S, A));;
gap> Length(C);
4
gap> M[1] in C;
true
gap> M[2] in C;
true
gap> ForAny(C, A -> Size(A) = 3^2 and IsElementaryAbelian(A));
true

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Centralizer(S, A) = Center(A));;
gap> C := Filtered(C, A -> RadicalTest(S, A));;
gap> Length(C);
13
gap> ForAll(C, A -> Index(S,A) <= 11);
true

gap> S := SmallGroup(5^5, 30);
<pc group of size 3125 with 5 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Centralizer(S, A) = Center(A));;
gap> C := Filtered(C, A -> RadicalTest(S, A));;
gap> Length(C);
12
gap> Number(C, A -> Size(A) = 25 and IsElementaryAbelian(A));
5
gap> Number(C, A -> Size(A) = 125 and IdGroup(A)[2] = 3);
5
gap> Number(C, A -> Size(A) = 5^4 and IsElementaryAbelian(A));
1
gap> S in C;
true

#
gap> STOP_TEST("RadicalTest.tst");
