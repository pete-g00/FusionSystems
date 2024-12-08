DeclareCategory("IsFusionSystem", IsObject);
BindGlobal("FusionSystemFamily", NewFamily("FusionSystemFamily"));

DeclareAttribute("UnderlyingGroup", IsFusionSystem);
DeclareAttribute("Prime", IsFusionSystem);
DeclareOperation("AutF", [IsFusionSystem, IsGroup]);
DeclareOperation("RepresentativeFIsomorphism", [IsFusionSystem, IsGroup, IsGroup]);
DeclareOperation("FClassReps", [IsFusionSystem, IsGroup]);
DeclareAttribute("FClassesReps", IsFusionSystem);

DeclareOperation("AreFConjugate", [IsFusionSystem, IsGroup, IsGroup]);
DeclareOperation("\in", [IsGroupHomomorphism, IsFusionSystem]);
DeclareOperation("IsFullyNormalized", [IsFusionSystem, IsGroup]);
DeclareOperation("IsFullyCentralized", [IsFusionSystem, IsGroup]);
DeclareOperation("IsFullyAutomized", [IsFusionSystem, IsGroup]);
DeclareOperation("ExtendMapToNPhi", [IsFusionSystem, IsGroupHomomorphism]);
DeclareOperation("IsFReceptive", [IsFusionSystem, IsGroup]);
DeclareOperation("IsFCentric", [IsFusionSystem, IsGroup]);
DeclareOperation("IsFRadical", [IsFusionSystem, IsGroup]);
DeclareOperation("IsFEssential", [IsFusionSystem, IsGroup]);
DeclareProperty("IsSaturated", IsFusionSystem);
DeclareOperation("\=", [IsFusionSystem, IsFusionSystem]);
DeclareOperation("IsomorphismFusionSystems", [IsFusionSystem, IsFusionSystem]);
