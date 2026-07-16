DeclareAttribute("Holomorph", IsPGroup);
DeclareOperation("Automizer", [IsGroup, IsGroup]);

DeclareGlobalFunction("OnQuotient");

# Computes C_G(A/U)
DeclareOperation("CentralizerMod", [IsGroup, IsGroup, IsGroup]);

DeclareGlobalFunction("OnImage");

DeclareGlobalFunction("OnImageNM");
