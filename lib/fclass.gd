DeclareCategory("IsFClass", IsCollection );
DeclareInfoClass("InfoFClass");

DeclareAttribute("Reps", IsFClass);
DeclareOperation("\=", [IsFClass, IsFClass]);
DeclareOperation("\in", [IsGroup, IsFClass]);
# up to Aut_F(S) conjugacy
DeclareOperation("ContainingFConjugates", [IsFClass, IsGroup]);
DeclareOperation("ContainedFConjugates", [IsFClass, IsGroup]);
DeclareOperation("FindMap", [IsFClass, IsGroup]);
DeclareProperty("IsCentric", IsFClass);
DeclareOperation("IsSaturated", [IsFClass, IsGroupOfAutomorphisms]);

DeclareGlobalFunction("OrbitUpToClass");

DeclareRepresentation("IsFClassRep",
    IsComponentObjectRep and IsFClass, ["G", "f", "A", "R", "S"]);
DeclareOperation("FClass", [IsGroup, IsGroupHomomorphism, IsGroup, IsRecord]);
