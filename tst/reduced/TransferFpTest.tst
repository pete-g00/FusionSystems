# FusionSystems, Reduced.gi, TransferFpTest
#
gap> START_TEST("TransferFpTest.tst"); 

gap> S := SmallGroup(128, 931);
<pc group of size 128 with 7 generators>
gap> L := AllProtoEssentials(S);;
gap> Length(L);
5
gap> A := Filtered(L, A -> Size(A) = 64);;
gap> TransferFpTest(S, A);
true
gap> A := Filtered(L, A -> Size(A) = 32);;
gap> TransferFpTest(S, A);
false
gap> TransferFpTest(S, []);
false

gap> S := DihedralGroup(2^7);
<pc group of size 128 with 7 generators>
gap> L := AllProtoEssentials(S);;
gap> TransferFpTest(S, L);
true
gap> TransferFpTest(S, L{[1]});
false

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> L := AllProtoEssentials(S);;
gap> V := First(L, A -> Size(A) = 3^2);;
gap> A := First(L, A -> Size(A) = 3^3 and IsElementaryAbelian(A));;
gap> W := First(L, A -> Size(A) = 3^3 and not IsElementaryAbelian(A));;
gap> TransferFpTest(S, [V]);
true
gap> TransferFpTest(S, [V, A]);
true
gap> TransferFpTest(S, [W, A]);
true
gap> TransferFpTest(S, []);
true

gap> S := SmallGroup(3^3, 3);
<pc group of size 27 with 3 generators>
gap> L := AllProtoEssentials(S);;
gap> TransferFpTest(S, L{[1]});
true
gap> TransferFpTest(S, L{[1,2]});
true
gap> TransferFpTest(S, L);
true
gap> TransferFpTest(S, []);
true

#
gap> STOP_TEST("TransferFpTest.tst", 1);
