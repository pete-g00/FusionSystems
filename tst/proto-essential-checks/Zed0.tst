# FusionSystems, ProtoEssentialChecks.gi, Zed0
#
gap> START_TEST("Zed0.tst");

gap> S := SmallGroup(64, 242);
<pc group of size 64 with 6 generators>
gap> Z0 := Zed0(S);;
gap> Z0 = Center(S);
true
gap> Z0 = FS_SecondCentre(S);
false

gap> S := SmallGroup(256, 5352);
<pc group of size 256 with 8 generators>
gap> Z0 := Zed0(S);;
gap> Z0 = Center(S);
false
gap> Z0 = FS_SecondCentre(S);
true

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> Z0 := Zed0(S);;
gap> Z0 = Center(S);
false
gap> Z0 = FS_SecondCentre(S);
true

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> Z0 := Zed0(S);;
gap> Z0 = Center(S);
false
gap> Z0 = S;
true

#
gap> STOP_TEST("Zed0.tst");
