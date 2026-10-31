# FusionSystems, ProtoEssentials.gi, GenerateProtoEssentials
#
gap> START_TEST("GenerateProtoEssentials.tst");

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
3
gap> SetInfoLevel(InfoFusion, 2);
gap> C := GenerateProtoEssentials(S, C);;
#I  Generating all proto-essential subgroups from 3 subgroups
#I      Failed centric test
#I      Failed centric test
#I      Failed centric test
#I      Failed centric test
#I      Failed centric test
#I  Generated 3 subgroups
gap> SetInfoLevel(InfoFusion, 0);
gap> ForAll(C, A -> IsProtoEssential(S, A));
true
gap> C := GenerateProtoEssentials(S, []);
[]

gap> S := DirectProduct(CyclicGroup(3), SmallGroup(3^3, 3));
<pc group of size 81 with 4 generators>
gap> C := MainProtoEssentials(S);;
gap> Length(C);
4
gap> SetInfoLevel(InfoFusion, 2);
gap> C := GenerateProtoEssentials(S, C);;
#I  Generating all proto-essential subgroups from 4 subgroups
#I  Generated 4 subgroups
gap> SetInfoLevel(InfoFusion, 0);

#
gap> STOP_TEST("GenerateProtoEssentials.tst");
