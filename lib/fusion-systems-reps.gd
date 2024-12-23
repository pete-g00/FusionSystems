DeclareRepresentation("IsSaturatedFusionSystemRep", 
    IsComponentObjectRep and IsFusionSystem, ["G", "f", "p", "S", "d"]);

DeclareOperation("FClass", [IsFusionSystem, IsGroup]);
DeclareOperation("\^", [IsGroup, IsFusionSystem]);
DeclareOperation("SaturatedFusionSystem", [IsGroup, IsList]);
DeclareOperation("IsSaturated", [IsFusionSystem, IsFClass]);
