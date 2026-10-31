# FusionSystems, ProtoEssentialChecks.gi, FrattiniTest
#
gap> START_TEST("FrattiniTest.tst");

gap> S := SmallGroup(64, 242);
<pc group of size 64 with 6 generators>
gap> M := MaximalSubgroups(S);;
gap> Number(M, A -> FrattiniTest(S, A));
0
gap> C := SubgroupsSolvableGroup(S);;
gap> Number(C, A -> FrattiniTest(S, A));
14

gap> S := SmallGroup(256, 5352);
<pc group of size 256 with 8 generators>
gap> M := MaximalSubgroups(S);;
gap> Number(M, A -> FrattiniTest(S, A));
4
gap> C := SubgroupsSolvableGroup(S);;
gap> Number(C, A -> FrattiniTest(S, A));
20

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> FrattiniTest(S, A));;
gap> Length(C);
5
gap> Number(C, A -> Size(A) = 3^2 and IsElementaryAbelian(A));
1

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> Number(C, A -> FrattiniTest(S, A));
12

gap> S := SmallGroup(5^5, 30);
<pc group of size 3125 with 5 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> Number(C, A -> FrattiniTest(S, A));
16

#
gap> STOP_TEST("FrattiniTest.tst");
