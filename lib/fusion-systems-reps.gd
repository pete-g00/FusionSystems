DeclareRepresentation("IsSaturatedFusionSystemRep", 
    IsComponentObjectRep and IsFusionSystem, ["G", "f", "p", "S", "d"]);

DeclareOperation("FClass", [IsFusionSystem, IsGroup]);
DeclareOperation("SaturatedFusionSystem", [IsGroup, IsList]);
