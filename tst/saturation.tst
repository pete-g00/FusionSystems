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

# only O_p(F) = 1
gap> List([7, 8, 9], i -> Length(AllSaturatedFusionSystems(SmallGroup(16, i) : CoreFree)));
[ 2, 2, 0 ]
gap> SortedList(List(AllSaturatedFusionSystems(SmallGroup(27, 3) : CoreFree), NumberOfCharactersOfFusionSystem));
[ 11, 13, 13, 14 ]

# only O^p(F) = F, and both conditions; the options agree with filtering the complete list
gap> List([7, 8, 9], i -> Length(AllSaturatedFusionSystems(SmallGroup(16, i) : FullFocal)));
[ 1, 1, 1 ]
gap> Length(AllSaturatedFusionSystems(SmallGroup(27, 3) : FullFocal));
12
gap> SortedList(List(AllSaturatedFusionSystems(SmallGroup(27, 3) : CoreFree, FullFocal), NumberOfCharactersOfFusionSystem));
[ 11, 13, 13, 14 ]
gap> ForAll([SmallGroup(16, 8), SmallGroup(27, 3), SmallGroup(81, 9)], function(S)
>      local L, foc, core;
>      L := AllSaturatedFusionSystems(S);
>      foc := Filtered(L, F -> FocalSubgroupOfFusionSystem(F) = S);
>      core := Filtered(foc, F -> Size(PCoreOfFusionSystem(F)) = 1);
>      return Length(foc) = Length(AllSaturatedFusionSystems(S : FullFocal)) and
>             Length(core) = Length(AllSaturatedFusionSystems(S : CoreFree, FullFocal)) and
>             Number(L, F -> Size(PCoreOfFusionSystem(F)) = 1) = Length(AllSaturatedFusionSystems(S : CoreFree));
>    end);
true

# 5^(1+2)_+
gap> Length(AllSaturatedFusionSystems(SmallGroup(125, 3)));
36

# overgroups with a given Sylow p-subgroup, up to N_G(T)-conjugacy
gap> G := SymmetricGroup(5);;
gap> List([SylowSubgroup(G, 2), Group((1,2,3)), Group((1,2)(3,4))], T -> Length(OvergroupsWithSylowSubgroup(G, T)));
[ 3, 9, 3 ]
gap> G := GL(2, 5);;
gap> SortedList(List(OvergroupsWithSylowSubgroup(G, SylowSubgroup(G, 5)), Size));
[ 5, 10, 10, 10, 20, 20, 20, 20, 20, 20, 20, 40, 40, 40, 80, 120, 240, 480 ]

#
gap> STOP_TEST("saturation.tst", 1);
