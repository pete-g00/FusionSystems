gap> START_TEST("saturation.tst");

# fusion systems of groups
gap> F := FusionSystemOfGroup(AlternatingGroup(6), 2);;
gap> IsSaturatedFusionSystem(F);
true
gap> SortedList(List(CentricSubgroupClassRepresentatives(F), Size));
[ 4, 4, 4, 8 ]
gap> FocalSubgroupOfFusionSystem(F) = UnderlyingPGroup(F);
true
gap> Size(PCoreOfFusionSystem(F));
1
gap> NumberOfWeightsOfFusionSystem(F);
3
gap> NumberOfCharactersOfFusionSystem(F);
5
gap> F := FusionSystemOfGroup(SymmetricGroup(4), 2);;
gap> Size(PCoreOfFusionSystem(F));
4
gap> NumberOfWeightsOfFusionSystem(F);
2
gap> IsomorphismFusionSystems(F, F) <> fail;
true
gap> NumberOfCharactersOfFusionSystem(FusionSystemOfGroup(MathieuGroup(11), 2));
8

# S = C2 x C2 is not fully automized if Aut_F(S) contains an involution
gap> S := SmallGroup(4, 2);;
gap> a := GroupHomomorphismByImages(S, S, GeneratorsOfGroup(S), Reversed(GeneratorsOfGroup(S)));;
gap> IsSaturatedFusionSystem(FusionSystemByAutomizers(S, [a], []));
false

# enumeration: D8, D16, SD16, Q16 and 3^(1+2)_+
gap> SortedList(List(AllSaturatedFusionSystems(SmallGroup(8, 3)), NumberOfCharactersOfFusionSystem));
[ 5, 5, 5 ]
gap> List([7, 8, 9], i -> Length(AllSaturatedFusionSystems(SmallGroup(16, i))));
[ 3, 4, 3 ]
gap> Length(AllSaturatedFusionSystems(SmallGroup(27, 3)));
15

#
gap> STOP_TEST("saturation.tst", 1);
