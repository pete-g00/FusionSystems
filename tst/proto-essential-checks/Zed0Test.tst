# FusionSystems, ProtoEssentialChecks.gi, Zed0Test
#
gap> START_TEST("Zed0Test.tst");

gap> S := SmallGroup(64, 242);
<pc group of size 64 with 6 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Zed0Test(S, A));;
gap> Length(C);
67

gap> S := SmallGroup(256, 5352);
<pc group of size 256 with 8 generators>
gap> M := MaximalSubgroups(S);;
gap> ForAny(M, A -> Zed0Test(S, A));
true
gap> Number(M, A -> Zed0Test(S, A));
7
gap> Length(M);
7
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Zed0Test(S, A));;
gap> Length(C);
68

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Zed0Test(S, A));;
gap> Length(C);
7

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Zed0Test(S, A));;
gap> Length(C);
13

gap> S := SmallGroup(5^5, 30);
<pc group of size 3125 with 5 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> Zed0Test(S, A));;
gap> Length(C);
20

#
gap> STOP_TEST("Zed0Test.tst");
