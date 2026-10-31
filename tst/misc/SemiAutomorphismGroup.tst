# FusionSystems, MISC.gi, SemiAutomorphismGroup
#
gap> START_TEST("SemiAutomorphismGroup.tst"); 

gap> S := TrivialGroup();
<pc group of size 1 with 0 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
1
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := AbelianGroup([2,2]);
<pc group of size 4 with 2 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
3
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
false

gap> S := AbelianGroup([4]);
<pc group of size 4 with 1 generator>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
1
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := DihedralGroup(8);
<pc group of size 8 with 3 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
4
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := SmallGroup(16, 8);
<pc group of size 16 with 4 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
8
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := DirectProduct(AbelianGroup([2]), DihedralGroup(8));
<pc group of size 16 with 4 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
4
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := SmallGroup(32, 2);
<pc group of size 32 with 5 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
48
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
false

gap> S := AbelianGroup([8,4]);
<pc group of size 32 with 2 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
1
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := SmallGroup(32, 4);
<pc group of size 32 with 5 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
4
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := DirectProduct(DihedralGroup(16), DihedralGroup(8));
<pc group of size 128 with 7 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
32
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := SmallGroup(64, 242); # Sylow-2 subgroup of PSL(3,4)
<pc group of size 64 with 6 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
2304
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
false

gap> S := SmallGroup(128, 934); # Sylow-2 subgroup of \Jn_2
<pc group of size 128 with 7 generators>
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
768
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
false

gap> S := SmallGroup(3^3, 3);
<pc group of size 27 with 3 generators>
gap> A := AutomorphismGroup(S);;
gap> Size(A);
432
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
72
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
false

gap> S := SmallGroup(5^3, 3);
<pc group of size 125 with 3 generators>
gap> A := AutomorphismGroup(S);;
gap> Size(A);
12000
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
3000
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
false

gap> S := SmallGroup(5^3, 4);
<pc group of size 125 with 3 generators>
gap> A := AutomorphismGroup(S);;
gap> Size(A);
500
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
25
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := SmallGroup(3^3, 4);
<pc group of size 27 with 3 generators>
gap> A := AutomorphismGroup(S);;
gap> Size(A);
54
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
9
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := SmallGroup(5^5, 38);
<pc group of size 3125 with 5 generators>
gap> A := AutomorphismGroup(S);;
gap> Size(A);
15625
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
625
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := SmallGroup(3^6, 31);
<pc group of size 729 with 6 generators>
gap> A := AutomorphismGroup(S);;
gap> Size(A);
19683
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
81
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := SmallGroup(3^6, 3);
<pc group of size 729 with 6 generators>
gap> A := AutomorphismGroup(S);;
gap> Size(A);
39366
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
9
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

gap> S := SmallGroup(3^6, 469); # Sylow 2-subgroup of PSL(3,9)
<pc group of size 729 with 6 generators>
gap> A := AutomorphismGroup(S);;
gap> Size(A);
75582720
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
4723920
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
false

gap> S := SmallGroup(5^6, 631);
<pc group of size 15625 with 6 generators>
gap> A := AutomorphismGroup(S);;
gap> Size(A);
6250000
gap> A := SemiAutomorphismGroup(S);;
gap> Size(A);
3125
gap> SemiAutomorphismGroup(S) = InnerAutomorphismGroup(S);
true

#
gap> STOP_TEST("SemiAutomorphismGroup.tst", 1);
