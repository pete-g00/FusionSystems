DeclareRepresentation("IsSaturatedFusionSystemRep", 
    IsComponentObjectRep and IsFusionSystem and IsAttributeStoringRep, ["essclasses", "knownclasses"]);

DeclareOperation("FClass", [IsFusionSystem, IsGroup]);
DeclareOperation("\^", [IsGroup, IsFusionSystem]);
DeclareOperation("SaturatedFusionSystem", [IsGroup, IsList]);
DeclareOperation("IsSaturated", [IsFusionSystem, IsFClass]);
