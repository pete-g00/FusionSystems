# FusionSystems, ProtoEssentials.gi, AllProtoEssentials
#
gap> START_TEST("AllProtoEssentials.tst");

gap> S := SmallGroup(128, 931);
<pc group of size 128 with 7 generators>
gap> C := AllProtoEssentials(S);;
gap> Length(C);
5
gap> ForAll(C, A -> IsProtoEssential(S, A));
true
gap> Number(C, A -> IdGroup(A) = [ 64, 242 ]);
1
gap> Number(C, A -> IdGroup(A) = [ 64, 138 ]);
2
gap> Number(C, A -> IdGroup(A) = [ 32, 27 ]);
2

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> C := AllProtoEssentials(S);;
gap> Length(C);
3
gap> ForAll(C, A -> IsProtoEssential(S, A));
true
gap> ForAny(C, A -> IdGroup(A) = [3^2, 2]);
true
gap> ForAny(C, A -> IdGroup(A) = [3^3, 5]);
true
gap> ForAny(C, A -> IdGroup(A) = [3^3, 3]);
true

gap> S := DirectProduct(CyclicGroup(3), SmallGroup(3^3, 3));
<pc group of size 81 with 4 generators>
gap> C := AllProtoEssentials(S);;
gap> Length(C);
4
gap> ForAll(C,  A -> Index(S,A) = 3 and IsElementaryAbelian(A));
true
gap> ForAll(C, A -> IsProtoEssential(S, A));
true

#
gap> STOP_TEST("AllProtoEssentials.tst");
