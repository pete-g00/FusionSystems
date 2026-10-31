# FusionSystems, Reduced.gi, SemiCharacteristicGeneratedTest
#
gap> START_TEST("SemiCharacteristicGeneratedTest.tst"); 

gap> S := SmallGroup(128, 931);
<pc group of size 128 with 7 generators>
gap> L := AllProtoEssentials(S);;
gap> Length(L);
5
gap> A := Filtered(L, A -> Size(A) = 64);;
gap> SemiCharacteristicGeneratedTest(S, A);
true
gap> A := Filtered(L, A -> Size(A) = 32);;
gap> SemiCharacteristicGeneratedTest(S, A);
false
gap> SemiCharacteristicGeneratedTest(S, []);
false

gap> S := DihedralGroup(2^7);
<pc group of size 128 with 7 generators>
gap> L := AllProtoEssentials(S);;
gap> SemiCharacteristicGeneratedTest(S, L);
true
gap> SemiCharacteristicGeneratedTest(S, L{[1]});
false

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> L := AllProtoEssentials(S);;
gap> V := First(L, A -> Size(A) = 3^2);;
gap> A := First(L, A -> Size(A) = 3^3 and IsElementaryAbelian(A));;
gap> W := First(L, A -> Size(A) = 3^3 and not IsElementaryAbelian(A));;
gap> SemiCharacteristicGeneratedTest(S, [V]);
true
gap> SemiCharacteristicGeneratedTest(S, [V, A]);
true
gap> SemiCharacteristicGeneratedTest(S, [W, A]);
true
gap> SemiCharacteristicGeneratedTest(S, []);
true

gap> S := SmallGroup(3^3, 3);
<pc group of size 27 with 3 generators>
gap> L := AllProtoEssentials(S);;
gap> SemiCharacteristicGeneratedTest(S, L{[1]});
true
gap> SemiCharacteristicGeneratedTest(S, L{[1,2]});
true
gap> SemiCharacteristicGeneratedTest(S, L);
true
gap> SemiCharacteristicGeneratedTest(S, []);
true

#
gap> STOP_TEST("SemiCharacteristicGeneratedTest.tst", 1);
