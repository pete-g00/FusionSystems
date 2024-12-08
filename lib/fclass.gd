DeclareCategory("IsFClass", IsCollection );
DeclareInfoClass("InfoFClass");

DeclareAttribute("Reps", IsFClass);
DeclareOperation("\=", [IsFClass, IsFClass]);
DeclareProperty("IsSaturated", IsFClass);
DeclareOperation("\in", [IsGroup, IsFClass]);
DeclareOperation("FindMap", [IsFClass, IsGroup]);

DeclareGlobalFunction("OrbitUpToClass");

DeclareRepresentation("IsFClassRep",
    IsComponentObjectRep and IsFClass, ["G", "f", "A", "R", "S"]);
DeclareOperation("FClass", [IsGroup, IsGroupHomomorphism, IsGroup, IsRecord]);
