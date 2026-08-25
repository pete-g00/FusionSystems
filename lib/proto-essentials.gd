DeclareInfoClass("InfoFusion");

#! @Description 
#! Checks whether $E$ is proto-essential in $S$. We do so by running a number of tests, given below. The algorithm avoids computing $\Aut(E)$ if possible.
#! @Arguments S E
#! @Returns true or false
DeclareOperation("IsProtoEssentialSubgroup", [IsPGroup, IsPGroup]);

#! @Description 
#! Checks whether $E$ is proto-essential in $S$. This is only valid if $S$ is a $2$-group of order $\leq 2^{10}$.
#! This operation does not require $\Aut(E)$.
#! 
#! @Arguments S E
#! @Returns true or false
DeclareOperation("PE_FAST2", [IsPGroup, IsPGroup]);

#! @Description 
#! Checks whether $E$ is proto-essential in $S$. This is only valid if $S$ is a $2$-group of order $\leq 2^{10}$.
#! This operation requires $\Aut(E)$.
#! 
#! @Arguments S E
#! @Returns true or false
DeclareOperation("PE_SLOW2", [IsPGroup, IsPGroup]);

#! @Description
#! Uses the list $L$ containing the main proto-essential subgroups of $S$ to generate all the proto-essential subgroups of $S$.
#! @Arguments S L
#! @Returns a list
DeclareOperation("GenerateProtoEssentials", [IsPGroup, IsList]);
