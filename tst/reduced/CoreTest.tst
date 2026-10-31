# FusionSystems, Reduced.gi, CoreTest
#
gap> START_TEST("CoreTest.tst"); 

gap> S := SmallGroup(128, 931);
<pc group of size 128 with 7 generators>
gap> L := AllProtoEssentials(S);;
gap> Length(L);
5
gap> A := Filtered(L, A -> Size(A) = 64);;
gap> CoreTest(S, A);
true
gap> A := Filtered(L, A -> Size(A) = 32);;
gap> CoreTest(S, A);
true
gap> CoreTest(S, []);
false

gap> S := DihedralGroup(2^7);
<pc group of size 128 with 7 generators>
gap> L := AllProtoEssentials(S);;
gap> CoreTest(S, L);
true
gap> CoreTest(S, L{[1]});
true

gap> S := DihedralGroup(2^7);
<pc group of size 128 with 7 generators>
gap> L := AllProtoEssentials(S);;
gap> CoreTest(S, L);
true
gap> CoreTest(S, L{[1]});
true

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> L := AllProtoEssentials(S);;
gap> V := First(L, A -> Size(A) = 3^2);;
gap> A := First(L, A -> Size(A) = 3^3 and IsElementaryAbelian(A));;
gap> W := First(L, A -> Size(A) = 3^3 and not IsElementaryAbelian(A));;
gap> CoreTest(S, [V]);
true
gap> CoreTest(S, [V, A]);
true
gap> CoreTest(S, [W, A]);
true
gap> CoreTest(S, []);
false

gap> S := SmallGroup(3^3, 3);
<pc group of size 27 with 3 generators>
gap> L := AllProtoEssentials(S);;
gap> CoreTest(S, L{[1]});
false
gap> CoreTest(S, L{[1,2]});
true
gap> CoreTest(S, L);
true
gap> CoreTest(S, []);
false

#
gap> STOP_TEST("CoreTest.tst", 1);
