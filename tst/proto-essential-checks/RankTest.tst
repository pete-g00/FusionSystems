# FusionSystems, ProtoEssentialChecks.gi, RankTest
#
gap> START_TEST("RankTest.tst");

gap> S := SmallGroup(64, 242);
<pc group of size 64 with 6 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Set(I) = Set([-1, 0, 1]);
true
gap> Number(I, A -> A = 0);
33
gap> Number(I, A -> A = 1);
2
gap> Number(I, A -> A = -1);
95

gap> S := SmallGroup(256, 5352);
<pc group of size 256 with 8 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Set(I) = Set([-1, 0, 1]);
true
gap> Number(I, A -> A = 0);
38
gap> Number(I, A -> A = 1);
2
gap> Number(I, A -> A = -1);
139

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Set(I) = Set([-1, 0]);
true
gap> Number(I, A -> A = 0);
9
gap> Number(I, A -> A = -1);
11

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Set(I) = Set([-1, 0]);
true
gap> Number(I, A -> A = 0);
12
gap> Number(I, A -> A = -1);
15

gap> S := SmallGroup(5^5, 30);
<pc group of size 3125 with 5 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> I := List(C, A -> RankTest(S, A));;
gap> Set(I) = Set([-1, 0]);
true
gap> Number(I, A -> A = 0);
47
gap> Number(I, A -> A = -1);
202

#
gap> STOP_TEST("RankTest.tst");
