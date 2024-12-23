#! @Chapter Miscellaneous functions
#! In this section, we define some functionalities about groups and group homomorphisms that are used in the main fusion systems package. It is hoped that these operations will be of use in general.

#! @Section Operations

#! @Description
#! Given a map $\phi \colon A \to B$ and an element $x \in A$, returns the evaluated value $x^\phi$.
#! @Arguments x phi
DeclareAttribute("IsomType", IsGroup);

#! @Description
#! Given a map $\phi \colon A \to B$ and an element $x \in A$, returns the evaluated value $x^\phi$.
#! @Arguments x phi
DeclareGlobalFunction("OnImage");

DeclareGlobalFunction("OnImageNM");

#! @Description
#! Given a map $\phi \colon A \to B$ and an list $L \subseteq A$, applies the map $\phi$ on each $L$.
#! @Arguments x phi
DeclareGlobalFunction("OnImageTuples");

DeclareGlobalFunction("OnImageTuplesNM");

#! @Description
#! Given a map $\phi \colon A \to B$ and a map $\psi \colon C \to D$, with $A, B \leq C$, 
#! returns the conjugated map $\phi^\psi \colon \psi(A) \to \psi(B)$
#! @Arguments phi psi
DeclareGlobalFunction("OnHomConjugation");

#! @Description
#! Given a list of maps $\phi_i \colon A_i \to B_i$ and a map $\psi \colon C \to D$, with $A_i, B_i \leq C$, 
#! returns the list of conjugated maps $\phi_i^\psi \colon \psi(A_i) \to \psi(B_i)$
#! @Arguments phi psi
DeclareGlobalFunction("OnHomListConjugation");

#! @Description
#! Given a group of automorphisms $A$ on the group $P$ and an isomorphism $\psi \colon P \to Q$, returns
#! the corresponding group of automorphism $\psi(A)$ of $Q$.
#! @Arguments A psi
DeclareGlobalFunction("OnAutGroupConjugation");

#! @Description
#! Given a group $P$, defines the action of $H \leq \Aut(P)$ on the conjugacy classes of $P$.
#! 
#! In particular, $H$ acts on a conjugacy class $Q^P$ by application, i.e. $\phi \cdot Q^P = (\phi(Q))^P$.
#! 
#! @Arguments P
DeclareGlobalFunction("OnCoCl");
DeclareGlobalFunction("OnCoClNM");
DeclareGlobalFunction("OnCoCle");

#! @Description
#! Given a homomorphism $\phi \colon P \to Q$, and $A \leq P$ and $Q \leq B$, 
#! returns the induced homomorphism $\psi \colon A \to B$.
#! 
#! This version does not check whether $A \leq P$ and $Q \leq B$.
#! @Arguments phi A B
DeclareOperation("RestrictedHomomorphismNC", [IsGroupHomomorphism, IsGroup, IsGroup]);

#! @Description
#! Given a homomorphism $\phi \colon P \to Q$, and $A \leq P$ and $Q \leq B$, 
#! returns the induced homomorphism $\psi \colon A \to B$.
#! 
#! This version checks whether $A \leq P$ and $Q \leq B$.
#! @Arguments phi A B
DeclareOperation("RestrictedHomomorphism", [IsGroupHomomorphism, IsGroup, IsGroup]);

# TODO: Improve code
# Given subgroups $A$ and $B$ of some group $G$, and a $g \in G$ such that 
# $A^g \leq B$, defines the homomorphism $A \to B$ by $a \mapsto a^g$
DeclareOperation("ConjugationHomomorphism", [IsGroup, IsGroup, IsObject]);

#! @Description
#! Given a prime power $q = p^n$, returns the prime $p$. If $q$ is not a prime power, then returns `fail`.
#! @Arguments q
DeclareOperation("FindPrimeOfPrimePower", [IsScalar]);

#! @BeginExample
#! gap> FindPrimeOfPrimePower(1024);
#! 2
#! gap> FindPrimeOfPrimePower(10);
#! fail
#! @EndExample

#! @BeginGroup Automizers
#! @Arguments G H
#! @Returns a group
DeclareOperation("Automizer", [IsGroup, IsGroup]);

#! @Description 
#! Let $G$ be a group, $H$ a subgroup of $G$, and $A \leq \Aut(G)$.
#! 
#! The operation `Automizer(G, H)` computes the automorphism group of $H$ induced by conjugation in $G$, denoted $\Aut_G(H)$. Specifically, we return the group
#! $$\Aut_G(H) = \{c_g \in \Aut(H) \mid g \in N_G(H)\},$$
#! where $c_g \in \Aut(H)$ is the map given by conjugation, i.e. $c_g(x) = x^g$ for $x \in H$.
#! 
#! The operation `Automizer(A, H)` returns the automorphism group of $H$ induced maps in $A$, denoted $\Aut_A(H)$. Specifically, we return the group
#! $$\Aut_A(H) = \{\phi \in \Aut(G) \mid \phi|_H \in \Aut(H)\},$$
#! 
#! @Arguments A H
#! @Returns a group
DeclareOperation("Automizer", [IsGroupOfAutomorphisms, IsGroup]);
#! @EndGroup

#! @Description
#! Given a group $G$ and a prime $p$, the operation `PrCore(G,p)` constructs the $p'$-core subgroup of $G$: $O_{p'}(G)$.
#!
#! @Arguments G p
#! @Returns a group
DeclareOperation("PrCore", [IsGroup, IsPosInt]);

#! @Description
#! Given a group $G$ and a prime $p$, the operation `PResidue(G,p)` constructs the $p'$-residue subgroup of $G$: $O^{p'}(G)$.
#!
#! @Arguments G p
#! @Returns a group
DeclareOperation("PResidue", [IsGroup, IsPosInt]);

#! @Description
#! Given a group $P$ and a map $\phi \colon A \to B$ with $A, B \leq P$, computes the group $N_\phi$ in $P$. 
#! @Arguments P phi 
#! @Returns a group
DeclareOperation("NPhi", [IsGroup, IsGroupHomomorphism]);

#! @Description
#! Given a group $S$, a subgroup $A \leq S$ and a subgroup $X \leq \Aut(A)$, constructs the subgroup
#! $$\{x \in X \mid N_x = N_S(A)\}.$$
#! @Arguments S X
#! @Returns a group
DeclareOperation("FindMaxNPhi", [IsGroup, IsGroupOfAutomorphisms]);

#! @Description
#! Let $G$ be a group, with subgroup $A$ and an automorphism $\phi \colon A \to A$. If $A \leq \Aut(G)$, then the operation `ExtendAut(phi, A)` extends the automorphism $\phi$ to an automorphism in $G$, using the maps in $A$. If we cannot find an extension, then the operation returns `fail`. If possible, the order of the extension is the same as the order of $\phi$.
#! 
#! @Arguments phi L
#! @Returns an automorphism or `fail`
DeclareOperation("ExtendAut", [IsGroupHomomorphism, IsGroup]);

# # FindNormalizingAutExtension => find an extension of phi : A -> B to psi : QA -> QB where psi normalizes Q
# DeclareOperation("FindNormalizingHomExtension", [IsGroupHomomorphism, IsCollection, IsGroup]);

# # FindNormalizingAutExtension => find an extension of phi : A -> B to psi : QA -> QB where psi centralizes Q
# DeclareOperation("FindCentralizingHomExtension", [IsGroupHomomorphism, IsCollection, IsGroup]);

# FindCentralizingAutExtension => find an extension of phi : A -> B to psi : QA -> QB where psi centralizes Q

#! @Description
#! Given a group $G$ and a prime $p$, checks whether $G$ has a strongly $p$-embedded subgroup.
#! @Arguments G p
#! @Returns `true` or `false`
DeclareOperation("HasStronglyPEmbeddedSubgroup", [IsGroup, IsScalar]);

#! @BeginExample
#! gap> P := Group((1,2,3), (1,3));
#! Group([ (1,2,3), (1,3) ])
#! gap> Q := Group(P.1);
#! Group([ (1,2,3) ])
#! gap> IsStronglyPEmbedded(P, Q, 2);
#! false
#! gap> IsStronglyPEmbedded(P, Q, 3);
#! true
#! @EndExample

#! @Description
#! Let $G$ be a group with $H \leq G$. The list $L$ consists of elements up to $H$-conjugacy. The operation `AscendReps(L, G, H)` returns a subset of $L$ that consists of an element up to $G$-conjugacy. This method only works if $H$ is subnormal in $G$. 
#! @Arguments L G H
#! @Returns a list
DeclareGlobalFunction("AscendReps");

#! @Description
#! Let $G$ be a group with $H \leq G$ The operation `DescendReps(x, G, H)` $G$-conjugates of $x$ that consists of a single element up to $H$-conjugacy. This method only works if $H$ is subnormal in $G$. 
#! @Arguments x G H
#! @Returns a list
DeclareGlobalFunction("DescendReps");

#! @Description
#! Let $G$ be a group and $f$ a boolean function on $G$. This function returns the set 
# $${x \in G | f(x)}$$
# given that it forms a subgroup of $G$. A subgroup $H$ might be given that is known to already satisfy this property. The function will not work if the elements in $G$ satisfying this property is not a subgroup.
#! @Arguments G f [H]
#! @Returns a group
DeclareGlobalFunction("FindSubgroup");
