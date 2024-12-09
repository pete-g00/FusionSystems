DeclareCategory("IsFClass", IsCollection );
DeclareInfoClass("InfoFClass");

DeclareAttribute("Reps", IsFClass);
DeclareOperation("\=", [IsFClass, IsFClass]);
DeclareOperation("IsSaturated", [IsFClass, IsGroupOfAutomorphisms]);
DeclareOperation("\in", [IsGroup, IsFClass]);
DeclareOperation("FindMap", [IsFClass, IsGroup]);
DeclareProperty("IsCentric", IsFClass);

DeclareGlobalFunction("OrbitUpToClass");

DeclareRepresentation("IsFClassRep",
    IsComponentObjectRep and IsFClass, ["G", "f", "A", "R", "S"]);
DeclareOperation("FClass", [IsGroup, IsGroupHomomorphism, IsGroup, IsRecord]);
