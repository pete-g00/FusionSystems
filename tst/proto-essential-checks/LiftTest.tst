# FusionSystems, ProtoEssentialChecks.gi, LiftTest
#
gap> START_TEST("LiftTest.tst");

gap> S := SmallGroup(64, 242);
<pc group of size 64 with 6 generators>
gap> M := MaximalSubgroups(S);;
gap> ForAll(M, A -> LiftTest(S, A, 0));
true
gap> ForAny(M, A -> LiftTest(S, A, -1));
false
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> LiftTest(S, C[i], I[i]));
35

gap> S := SmallGroup(256, 5352);
<pc group of size 256 with 8 generators>
gap> M := MaximalSubgroups(S);;
gap> ForAll(M, A -> LiftTest(S, A, 0));
true
gap> ForAny(M, A -> LiftTest(S, A, -1));
false
gap> C := SubgroupsSolvableGroup(S);;
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> LiftTest(S, C[i], I[i]));
38

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> LiftTest(S, C[i], I[i]));
9

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> LiftTest(S, C[i], I[i]));
12

gap> S := SmallGroup(5^5, 30);
<pc group of size 3125 with 5 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Number([1..Length(I)], i -> LiftTest(S, C[i], I[i]));
47

#
gap> STOP_TEST("LiftTest.tst");
