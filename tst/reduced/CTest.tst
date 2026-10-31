# FusionSystems, Reduced.gi, CTest
#
gap> START_TEST("CTest.tst"); 

gap> S := DihedralGroup(16);
<pc group of size 16 with 4 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
2
gap> CTest(S, C);
true

gap> S := SmallGroup(16, 3);
<pc group of size 16 with 4 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
1
gap> Size(C[1]);
8
gap> CTest(S, C);
false

gap> S := SmallGroup(32, 9);
<pc group of size 32 with 5 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
1
gap> Size(C[1]);
8
gap> CTest(S, C);
false

gap> S := SmallGroup(32, 11); # C4 \wr C2
<pc group of size 32 with 5 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
2
gap> CTest(S, C);
true

gap> S := SmallGroup(128, 931); # Syl-2 of $\Mt_{22}$
<pc group of size 128 with 7 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
5
gap> CTest(S, C);
true

gap> S := SmallGroup(32, 5); 
<pc group of size 32 with 5 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
1
gap> CTest(S, C);
false

gap> S := SmallGroup(32, 16); 
<pc group of size 32 with 5 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
0
gap> CTest(S, C);
false

gap> S := SmallGroup(3^3, 3);
<pc group of size 27 with 3 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
4
gap> CTest(S, C);
true

gap> S := SmallGroup(5^3, 3);
<pc group of size 125 with 3 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
6
gap> CTest(S, C);
true

gap> S := SmallGroup(3^3, 4);
<pc group of size 27 with 3 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
1
gap> CTest(S, C);
false

gap> S := SmallGroup(5^3, 4);
<pc group of size 125 with 3 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
1
gap> CTest(S, C);
false

gap> S := SmallGroup(3^5, 5); 
<pc group of size 243 with 5 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
0
gap> CTest(S, C);
false

gap> S := SmallGroup(3^5, 16); 
<pc group of size 243 with 5 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
1
gap> CTest(S, C);
false

gap> S := SmallGroup(5^5, 5); 
<pc group of size 3125 with 5 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
2
gap> CTest(S, C);
true

gap> S := SmallGroup(5^5, 16); 
<pc group of size 3125 with 5 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
0
gap> CTest(S, C);
false

#
gap> STOP_TEST("CTest.tst", 1);
