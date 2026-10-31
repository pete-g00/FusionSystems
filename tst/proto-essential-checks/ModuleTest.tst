# FusionSystems, ProtoEssentialChecks.gi, ModuleTest
#
gap> START_TEST("ModuleTest.tst");

gap> S := SmallGroup(64, 242);
<pc group of size 64 with 6 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> Number(C, A -> ModuleTest(S, A));
36

gap> S := SmallGroup(256, 5352);
<pc group of size 256 with 8 generators>
gap> C := SubgroupsSolvableGroup(S);;
gap> Number(C, A -> ModuleTest(S, A));
39

#
gap> STOP_TEST("ModuleTest.tst");
