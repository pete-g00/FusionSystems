# FusionSystems, MISC.gi, SemiCharacteristicSubgroups
#
gap> START_TEST("SemiCharacteristicSubgroups.tst"); 

gap> S := TrivialGroup();
<pc group of size 1 with 0 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
1
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := AbelianGroup([2,2]);
<pc group of size 4 with 2 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
2
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := AbelianGroup([4]);
<pc group of size 4 with 1 generator>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
3
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := DihedralGroup(8);
<pc group of size 8 with 3 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
6
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(16, 8);
<pc group of size 16 with 4 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
7
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := DirectProduct(AbelianGroup([2]), DihedralGroup(8));
<pc group of size 16 with 4 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
19
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(32, 2);
<pc group of size 32 with 5 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
5
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := AbelianGroup([8,4]);
<pc group of size 32 with 2 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
22
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(32, 4);
<pc group of size 32 with 5 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
18
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := DirectProduct(DihedralGroup(16), DihedralGroup(8));
<pc group of size 128 with 7 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
104
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(64, 242); # Sylow-2 subgroup of PSL(3,4)
<pc group of size 64 with 6 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
5
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(128, 934); # Sylow-2 subgroup of \Jn_2
<pc group of size 128 with 7 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
7
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(3^3, 3);
<pc group of size 27 with 3 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
3
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(5^3, 3);
<pc group of size 125 with 3 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
3
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(5^3, 4);
<pc group of size 125 with 3 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
9
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(3^3, 4);
<pc group of size 27 with 3 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
7
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(5^5, 38);
<pc group of size 3125 with 5 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
11
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(3^6, 31);
<pc group of size 729 with 6 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
46
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(3^6, 3);
<pc group of size 729 with 6 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
49
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(3^6, 469); # Sylow 2-subgroup of PSL(3,9)
<pc group of size 729 with 6 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
7
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

gap> S := SmallGroup(5^6, 631);
<pc group of size 15625 with 6 generators>
gap> N := SemiCharacteristicSubgroups(S);;
gap> Length(N);
12
gap> ForAll(N, A -> IsNormal(S, A));
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := Filtered(C, A -> IsSemiCharacteristic(S, A));;
gap> Set(N) = Set(C);
true
gap> C := SubgroupsSolvableGroup(S);;
gap> C := List(C, A -> SemiCharacteristicClosure(S, A));;
gap> Set(N) = Set(C);
true

#
gap> STOP_TEST("SemiCharacteristicSubgroups.tst", 1);
