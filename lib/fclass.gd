DeclareCategory("IsFClass", IsCollection);
DeclareInfoClass("InfoFClass");

DeclareRepresentation("IsFClassRep",
    IsComponentObjectRep and IsAttributeStoringRep and IsFClass, ["data"]);
DeclareOperation("FClass", [IsGroup, IsRecord, IsGroup]);

DeclareGlobalFunction("AutomizerClass");

DeclareAttribute("Representative", IsFClass);
DeclareAttribute("AutF", IsFClass);
DeclareAttribute("UnderlyingFusionSystem", IsFClass);

DeclareOperation("\=", [IsFClass, IsFClass]);
DeclareOperation("\in", [IsGroup, IsFClass]);

DeclareOperation("FindMap", [IsFClass, IsGroup]);
DeclareProperty("IsCentric", IsFClass);
DeclareProperty("IsSaturated", IsFClass);
DeclareProperty("IsRadical", IsFClass);
