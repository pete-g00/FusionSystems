# FusionSystems, Reduced.gi, PossiblySupportsReducedFusionSystems_PE
#
gap> START_TEST("PossiblySupportsReducedFusionSystems_PE.tst"); 

gap> S := SmallGroup(128, 931);
<pc group of size 128 with 7 generators>
gap> L := AllProtoEssentials(S);;
gap> Length(L);
5
gap> A := Filtered(L, A -> Size(A) = 64);;
gap> PossiblySupportsReducedFusionSystems_PE(S, A);
true
gap> A := Filtered(L, A -> Size(A) = 32);;
gap> PossiblySupportsReducedFusionSystems_PE(S, A);
false
gap> PossiblySupportsReducedFusionSystems_PE(S, []);
false

gap> S := DihedralGroup(2^7);
<pc group of size 128 with 7 generators>
gap> L := AllProtoEssentials(S);;
gap> PossiblySupportsReducedFusionSystems_PE(S, L);
true
gap> PossiblySupportsReducedFusionSystems_PE(S, L{[1]});
false

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> L := AllProtoEssentials(S);;
gap> V := First(L, A -> Size(A) = 3^2);;
gap> A := First(L, A -> Size(A) = 3^3 and IsElementaryAbelian(A));;
gap> W := First(L, A -> Size(A) = 3^3 and not IsElementaryAbelian(A));;
gap> PossiblySupportsReducedFusionSystems_PE(S, [V]);
true
gap> PossiblySupportsReducedFusionSystems_PE(S, [V, A]);
true
gap> PossiblySupportsReducedFusionSystems_PE(S, [W, A]);
true
gap> PossiblySupportsReducedFusionSystems_PE(S, []);
false

gap> S := SmallGroup(3^3, 3);
<pc group of size 27 with 3 generators>
gap> L := AllProtoEssentials(S);;
gap> PossiblySupportsReducedFusionSystems_PE(S, L{[1]});
false
gap> PossiblySupportsReducedFusionSystems_PE(S, L{[1,2]});
true
gap> PossiblySupportsReducedFusionSystems_PE(S, L);
true
gap> PossiblySupportsReducedFusionSystems_PE(S, []);
false

#
gap> STOP_TEST("PossiblySupportsReducedFusionSystems_PE.tst", 1);
