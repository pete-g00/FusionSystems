# FusionSystems, Reduced.gi, C0Test
#
gap> START_TEST("C0Test.tst"); 

gap> S := DihedralGroup(16);
<pc group of size 16 with 4 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
2
gap> C0Test(S, C0);
true

gap> S := SmallGroup(32, 11); # C4 \wr C2
<pc group of size 32 with 5 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
1
gap> C0Test(S, C0);
true

gap> S := SmallGroup(128, 931); # Syl-2 of $\Mt_{22}$
<pc group of size 128 with 7 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
3
gap> C0Test(S, C0);
true

gap> S := SmallGroup(32, 5); 
<pc group of size 32 with 5 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
1
gap> C0Test(S, C0);
true

gap> S := SmallGroup(32, 16); 
<pc group of size 32 with 5 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
0
gap> C0Test(S, C0);
false

gap> S := SmallGroup(32, 44); 
<pc group of size 32 with 5 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
1
gap> C0Test(S, C0);
false

gap> S := SmallGroup(3^3, 3);
<pc group of size 27 with 3 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
4
gap> C0Test(S, C0);
true

gap> S := SmallGroup(5^3, 3);
<pc group of size 125 with 3 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
6
gap> C0Test(S, C0);
true

gap> S := SmallGroup(3^3, 4);
<pc group of size 27 with 3 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
1
gap> C0Test(S, C0);
true

gap> S := SmallGroup(5^3, 4);
<pc group of size 125 with 3 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
1
gap> C0Test(S, C0);
true

gap> S := SmallGroup(3^5, 5); 
<pc group of size 243 with 5 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
0
gap> C0Test(S, C0);
false

gap> S := SmallGroup(3^5, 16); 
<pc group of size 243 with 5 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
1
gap> C0Test(S, C0);
false

gap> S := SmallGroup(5^5, 5); 
<pc group of size 3125 with 5 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
1
gap> C0Test(S, C0);
true

gap> S := SmallGroup(5^5, 16); 
<pc group of size 3125 with 5 generators>
gap> C0 := MainProtoEssentials(S, 0);;
gap> Length(C0);
0
gap> C0Test(S, C0);
false

#
gap> STOP_TEST("C0Test.tst", 1);
