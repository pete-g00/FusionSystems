DeclareAttribute("Holomorph", IsPGroup);
DeclareOperation("Automizer", [IsGroup, IsGroup]);

DeclareGlobalFunction("OnQuotient");

# Computes C_G(A/U)
DeclareOperation("CentralizerMod", [IsGroup, IsGroup, IsGroup]);

DeclareGlobalFunction("OnImage");

DeclareGlobalFunction("OnImageNM");

DeclareGlobalFunction("OnImageTuples");

DeclareGlobalFunction("OnImageTuplesNM");

# TODO: The NC versions that don't do the checks
DeclareOperation("RestrictedAutomorphism", [IsGroupHomomorphism and IsBijective, IsGroup]);

DeclareOperation("RestrictedAutomorphismSubgroup", [IsGroupOfAutomorphismsFiniteGroup, IsGroup and IsFinite]);

DeclareOperation("RestrictedAutomorphismStabilizerSubgroup", [IsGroupOfAutomorphismsFiniteGroup, IsGroup and IsFinite]);
