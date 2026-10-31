# FusionSystems, ProtoEssentialChecks.gi, ValidAutTest
#
gap> START_TEST("ValidAutTest.tst");

gap> S := SmallGroup(64, 242);
<pc group of size 64 with 6 generators>
gap> M := MaximalSubgroups(S);;
gap> Number(M, A -> ValidAutTest(S, A, 0));
6
gap> Number(M, A -> ValidAutTest(S, A, -1));
0
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> ValidAutTest(S, C[i], I[i]));
17

gap> S := SmallGroup(256, 5352);
<pc group of size 256 with 8 generators>
gap> M := MaximalSubgroups(S);;
gap> Number(M, A -> ValidAutTest(S, A, 0));
1
gap> Number(M, A -> ValidAutTest(S, A, -1));
0
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> ValidAutTest(S, C[i], I[i]));
6

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> ValidAutTest(S, C[i], I[i]));
7
gap> Number(C, A -> Size(A) = 3^2 and IsElementaryAbelian(A));
6

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> ValidAutTest(S, C[i], I[i]));
12

gap> S := SmallGroup(5^5, 30);
<pc group of size 3125 with 5 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> ValidAutTest(S, C[i], I[i]));
42

#
gap> STOP_TEST("ValidAutTest.tst");
