# FusionSystems, Reduced.gi, ValidAutTest
#
gap> START_TEST("ValidAutTest.tst"); 

gap> S := TrivialGroup();
<pc group of size 1 with 0 generators>
gap> ValidAutTest(S);
false

gap> S := AbelianGroup([2,2]);
<pc group of size 4 with 2 generators>
gap> ValidAutTest(S);
false

gap> S := AbelianGroup([4]);
<pc group of size 4 with 1 generator>
gap> ValidAutTest(S);
false

gap> S := DihedralGroup(8);
<pc group of size 8 with 3 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(16, 8);
<pc group of size 16 with 4 generators>
gap> ValidAutTest(S);
true

gap> S := DirectProduct(AbelianGroup([2]), DihedralGroup(8));
<pc group of size 16 with 4 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(32, 2);
<pc group of size 32 with 5 generators>
gap> ValidAutTest(S);
true

gap> S := AbelianGroup([8,4]);
<pc group of size 32 with 2 generators>
gap> ValidAutTest(S);
false

gap> S := SmallGroup(32, 4);
<pc group of size 32 with 5 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(32, 8);
<pc group of size 32 with 5 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(32, 17);
<pc group of size 32 with 5 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(32, 11); # C_4 \wr C_2
<pc group of size 32 with 5 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(32, 12);
<pc group of size 32 with 5 generators>
gap> ValidAutTest(S);
true

gap> S := DirectProduct(DihedralGroup(16), DihedralGroup(8));
<pc group of size 128 with 7 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(64, 242); # Sylow-2 subgroup of PSL(3,4)
<pc group of size 64 with 6 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(128, 67); # C_8 \wr C_2
<pc group of size 128 with 7 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(128, 931); # Sylow-2 subgroup of M22
<pc group of size 128 with 7 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(3^3, 3);
<pc group of size 27 with 3 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(5^3, 3);
<pc group of size 125 with 3 generators>
gap> ValidAutTest(S);
true

gap> S := DirectProduct(CyclicGroup(3), SmallGroup(3^3, 3));
<pc group of size 81 with 4 generators>
gap> ValidAutTest(S);
true

gap> S := DirectProduct(CyclicGroup(5), SmallGroup(5^3, 3));
<pc group of size 625 with 4 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(5^3, 4);
<pc group of size 125 with 3 generators>
gap> ValidAutTest(S);
false

gap> S := SmallGroup(3^3, 4);
<pc group of size 27 with 3 generators>
gap> ValidAutTest(S);
false

gap> S := SmallGroup(5^4, 7);
<pc group of size 625 with 4 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(5^5, 38);
<pc group of size 3125 with 5 generators>
gap> ValidAutTest(S);
false

gap> S := SmallGroup(3^6, 31);
<pc group of size 729 with 6 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(3^6, 3);
<pc group of size 729 with 6 generators>
gap> ValidAutTest(S);
false

gap> S := SmallGroup(3^6, 41);
<pc group of size 729 with 6 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(3^6, 135);
<pc group of size 729 with 6 generators>
gap> ValidAutTest(S);
false

gap> S := SmallGroup(3^6, 469); # Sylow 2-subgroup of PSL(3,9)
<pc group of size 729 with 6 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(5^6, 232);
<pc group of size 15625 with 6 generators>
gap> ValidAutTest(S);
false

gap> S := SmallGroup(5^6, 631);
<pc group of size 15625 with 6 generators>
gap> ValidAutTest(S);
true

gap> S := SmallGroup(5^6, 662);
<pc group of size 15625 with 6 generators>
gap> ValidAutTest(S);
false

#
gap> STOP_TEST("ValidAutTest.tst", 1);
