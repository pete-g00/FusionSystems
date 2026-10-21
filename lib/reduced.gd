#! @Chapter Checks for reduced fusion systems

#! In this chapter, we describe all the tests currently implemented in GAP that test whether a group $S$ 
#! **could** support reduced fusion systems. This is done without constructing the fusion systems, and 
#! even possible automizers for any fusion system. As such, we can determine whether there exists any reduced fusion 
#! system $\mathcal{F}$ on $S$ for a fixed choice of $\mathcal{E}(\mathcal{F})$. We can also determine this 
#! for any choice of $\mathcal{E}(\mathcal{F})$.

#! @Section The main functions

#! @Description 
#! 
#! Given a $p$-group $S$, the attribute `PossiblySupportsReducedFusionSystems` checks whether $S$ **could** support reduced fusion systems.
#! 
#! Note that it is not possible to check whether a group can support reduced fusion systems without actually constructing them.
#! This is because the expected automizer sequences that lead to reduced fusion systems may not be saturated, and the only 
#! way we can discover this is by checking some radical, non-essential, subgroup in the expected saturated fusion system. 
#! Nonetheless, $p$-groups that pass the tests in this chapter are quite likely to support reduced fusion systems. 
#!
#! This function checks whether the group $S$ satisfies certain properties that are known to hold for a $p$-group that 
#! supports reduced fusion systems. In the process, we compute the proto-essential subgroups of $S$, along with their 
#! automorphism groups. 
#! @BeginLatexOnly
#! See \ref{Section_RedSpecificFn} for the list of specific tests currently implemented.
#! @EndLatexOnly
#! @BeginNotLatex
#! See <Label Ref="Section_RedSpecificFn" /> for the list of specific tests currently implemented.
#! @EndNotLatex
#! We do not construct automizer sequences.
#! 
#! @Arguments S
#! @Returns true or false
DeclareAttribute("PossiblySupportsReducedFusionSystems", IsPGroup);

#! @BeginExampleSession
#! gap> S := SmallGroup(2^7, 931);
#! <pc group of size 128 with 7 generators>
#! gap> PossiblySupportsReducedFusionSystems(S);
#! true
#! @EndExampleSession 

#! @Description 
#! 
#! Given a $p$-group $S$ and a list of proto-essential subgroups $L$, the attribute 
#! `PossiblySupportsReducedFusionSystems_PE` checks whether there **could** exist a reduced fusion system $\mathcal{F}$ 
#! on $S$ where the set of essential subgroups $\mathcal{E}(\mathcal{F})$ is a subset of $L$. Note that we run 
#! `GenerateProtoEssentials` on $L$ (which can, in theory, increase the number of subgroups in $L$).
#! 
#! Note that it is not possible to check whether a group can support reduced fusion systems without actually constructing them.
#! This is because the expected automizer sequences that lead to reduced fusion systems may not be saturated, and the only way 
#! we can discover this is by checking some radical, non-essential, subgroup in the expected saturated fusion system. 
#! Nonetheless, $p$-groups that pass the tests in this chapter are quite likely to support reduced fusion systems. 
#!
#! This function checks whether the group $S$ satisfies certain properties that are known to hold for a $p$-group that 
#! supports reduced fusion systems. We also construct the automorphism group for subgroups in $L$s. See ... for the list 
#! of specific tests currently implemented. We do not construct automizer sequences.
#! 
#! @Arguments S L
#! @Returns true or false
DeclareOperation("PossiblySupportsReducedFusionSystems_PE", [IsPGroup, IsList]);

#! @BeginExampleSession
#! gap> S := SmallGroup(2^7, 931);
#! <pc group of size 128 with 7 generators>
#! gap> L := AllProtoEssentials(S);
#! [ Group([ f7, f1, f2, f4, f5, f6 ]), Group([ f5, f6, f7, f1, f3, f4 ]), 
#! Group([ f5, f6, f7, f2, f3, f4 ]), Group([ f1, f2, f4, f6, f7 ]), 
#! Group([ f1, f3, f5, f6, f7 ]) ]
#! gap> PossiblySupportsReducedFusionSystems_PE(S, L{[1..3]});
#! true
#! gap> PossiblySupportsReducedFusionSystems_PE(S, L{[3..5]});
#! false
#! @EndExampleSession 

#! @Section The specific functions
#! @SectionLabel RedSpecificFn

#! @Description 
#! 
#! Given a $p$-group $S$, the attribute `IsDSWGroup` checks whether $p=2$, and that $S$ is isomorphic to dihedral, semi-dihedral group, or the 
#! wreath product $C_{2^a} \wr C_2$.
#! 
#! Using the work of Oliver and his collaborators, there are many properties on a $2$-group $S$ that imply that, if $S$ supports reduced fusion systems,
#! then $S$ is isomorphic to one of the three groups (and is called a $\mathcal{DSW}$-group) (see, for example, <Cite Key="AOV13" Where="Proposition 5.2" />).
#! 
#! @Arguments S
#! @Returns true or false
DeclareAttribute("IsDSWGroup", IsPGroup);

#! @BeginExampleSession
#! gap> S := DihedralGroup(2^3);
#! <pc group of size 8 with 3 generators>
#! gap> IsDSWGroup(S);
#! true
#! gap> S := SmallGroup(2^4, 8);
#! <pc group of size 16 with 4 generators>
#! gap> IsDSWGroup(S);
#! true
#! gap> S := QuaternionGroup(2^5);
#! <pc group of size 32 with 5 generators>
#! gap> IsDSWGroup(S);
#! false
#! gap> S := WreathProduct(CyclicGroup(IsPermGroup, 2^3), Group((1,2)));
#! Group([ (1,2,3,4,5,6,7,8), (9,10,11,12,13,14,15,16), 
#! (1,9)(2,10)(3,11)(4,12)(5,13)(6,14)(7,15)(8,16) ])
#! gap> IdGroup(S);
#! [128, 67]
#! gap> IsDSWGroup(S);
#! true
#! gap> S := SmallGroup(2^7, 437);
#! <pc group of size 128 with 7 generators>
#! gap> StructureDescription(S);
#! "(C8 x C8) : C2"
#! gap> IsDSWGroup(S);
#! false
#! @EndExampleSession 

#! @Description 
#! 
#! Let $S$ be a $p$-group. If $S$ has class $a$, the attribute `RED_ExponentTest` checks that $\Omega(Z(S))$ has exponent at most $p^t$, where 
#! $$t := \left\lceil \frac{c-1}{p-1} \right\rceil.$$
#! 
#! This test applies at any prime $p$. It is based on <Cite Key="LP" Where="Theorem A" />.
#! 
#! @Arguments S
#! @Returns true or false
DeclareAttribute("RED_ExponentTest", IsPGroup);

#! @BeginExampleSession
#! gap> S := SmallGroup(3^4, 13);
#! <pc group of size 81 with 4 generators>
#! gap> StructureDescription(S);
#! "C3 x (C9 : C3)"
#! gap> RED_ExponentTest(S);
#! true
#! gap> S := SmallGroup(3^4, 14);
#! <pc group of size 81 with 4 generators>
#! gap> StructureDescription(S);
#! "(C9 x C3) : C3"
#! gap> RED_ExponentTest(S);
#! false
#! @EndExampleSession 

#! @Description 
#! 
#! Let $S$ be a $2$-group. The attribute `RED_AbelianTest` first asserts whether there exists an abelian subgroup $A$ of $S$ satisfying $[N_S(A) : A] = 2$ and: 
#! * $N_S(A) = S$; or
#! * $N_S(A) &lt; S$, with $\mathrm{Aut}_S(A) \nleq O_2(\mathrm{Aut})(A)$.
#! If so, the function return true only if $S$ is a $\mathcal{DSW}$-group.
#! 
#! This test only applies at $p=2$. It is based on <Cite Key="AOV13" Where="Proposition 5.2(a), (c)" />.
#! 
#! @Arguments S
#! @Returns true or false
DeclareAttribute("RED_AbelianTest", IsPGroup);

#! @BeginExampleSession
#! gap> S := DihedralGroup(2^4);
#! <pc group of size 16 with 4 generators>
#! gap> RED_AbelianTest(S);
#! true
#! gap> S := SmallGroup(2^5, 9);
#! <pc group of size 32 with 5 generators>
#! gap> StructureDescription(S);
#! "(C8 x C2) : C2"
#! gap> StructureDescription(Center(S));
#! "C2 x C2"
#! gap> RED_AbelianTest(S);
#! false
#! @EndExampleSession 

#! @Description 
#! 
#! Let $S$ be a $p$-group. If $S'$ is cyclic, then the attribute `RED_DerivedCyclicTest` returns true only if:
#! * $S$ is a $\mathcal{DSW}$-group; or
#! * $S$ has an abelian subgroup of index $p$ (at $p$ odd).
#! 
# TODO: The odd proof after the paper is out
#! This test applies at any prime $p$. It is based on <Cite Key="AOV13" Where="Proposition 5.2(b)" /> (if $p=2$).
#! 
#! @Arguments S
#! @Returns true or false
DeclareAttribute("RED_DerivedCyclicTest", IsPGroup);

#! @BeginExampleSession
#! gap> S := DihedralGroup(2^4);
#! <pc group of size 16 with 4 generators>
#! gap> RED_DerivedCyclicTest(S);
#! true
#! gap> S := SmallGroup(2^5, 9);
#! <pc group of size 32 with 5 generators>
#! gap> StructureDescription(S);
#! "(C8 x C2) : C2"
#! gap> StructureDescription(Center(S));
#! "C2 x C2"
#! gap> RED_DerivedCyclicTest(S);
#! false
#! @EndExampleSession 

#! @Description 
#! 
#! Let $S$ be a $p$-group (for $p$ odd). The attribute `RED_ValidAutTest` returns true only if $\mathrm{Aut}(S)$ is 
#! not a $p$-group.
#! 
# TODO: Proof for valid aut test at $p=3$.
# TODO: We need to deal with - class $< p$ [\Aut(S), H] < S$ for $p$'-sub of $\Aut(S)$ => invalid
#! This test does not apply at $p=2$. It is based on <Cite Key="CRA" Where="7.82" /> (for $p \geq 5$).
#! 
#! @Arguments S
#! @Returns true or false
DeclareAttribute("RED_ValidAutTest", IsPGroup);

#! @BeginExampleSession
#! gap> S := SmallGroup(5^5, 38);
#! <pc group of size 3125 with 5 generators>
#! gap> NilpotencyClassOfGroup(S);
#! 4
#! gap> AutomorphismGroup(S);
#! <group of size 15625 with 6 generators>
#! gap> RED_ValidAutTest(S);
#! false
#! gap> S := SmallGroup(5^5, 30);
#! <pc group of size 3125 with 5 generators>
#! gap> NilpotencyClassOfGroup(S);
#! 4
#! gap> AutomorphismGroup(S);
#! <group of size 1250000 with 11 generators>
#! gap> RED_ValidAutTest(S);
#! true
#! gap> S := SmallGroup(5^5, 32);
#! <pc group of size 3125 with 5 generators>
#! gap> NilpotencyClassOfGroup(S);
#! 4
#! gap> AutomorphismGroup(S);
#! <group of size 62500 with 8 generators>
#! gap> RED_ValidAutTest(S);
#! false
#! @EndExampleSession 

#! @Description 
#! 
#! Let $S$ be a $2$-group, $D := S'$ and $O := \Omega(Z(S))$. The attribute `RED_OmegaAbelianizationTest` return false only if:
#! * $[\Omega(Z(S)) : \Omega(Z(S)) \cap D] = 2$; or
#! * $\Omega(Z(S)) \nleq D$ if $\mathrm{Aut}(S)$ is a $2$-group.
#! 
#! This test only applies at $p=2$. It is based on <Cite Key="AKO" Where="Corollary I.8.5" />.
#! 
#! @Arguments S
#! @Returns true or false
DeclareAttribute("RED_OmegaAbelianizationTest", IsPGroup);

#! @BeginExampleSession
#! gap> S := DihedralGroup(2^4);
#! <pc group of size 16 with 4 generators>
#! gap> RED_OmegaAbelianizationTest(S);
#! true
#! gap> S := SmallGroup(2^4, 3);
#! <pc group of size 16 with 4 generators>
#! gap> StructureDescription(S);
#! "(C4 x C2) : C2"
#! gap> RED_OmegaAbelianizationTest(S);
#! false
#! @EndExampleSession 

#! @BeginGroup 
#! @GroupTitle  Transfer test for a group

#! @Description 
#! 
#! Let $S$ be a $2$-group. The attribute `RED_TransferMaximalTest` checks that, if $\mathrm{Aut}(S)$ is a $2$-group, then
#! $$\bigcap_{M \in \mathcal{M}(S)} \ker(\mathrm{tr}_M^S) = S',$$
#! where $\mathcal{M}(S)$ is the set of maximal subgroups of $S$, and 
#! $\mathrm{tr}_M^S \colon S \to M/M'$ is the transfer homomorphism. Alternatively, 
#! `RED_TransferFpMaximalTest` checks that, if $\mathrm{Aut}(S)$ is a $2$-group, then
#! $$\bigcap_{M \in \mathcal{M}(S)} \ker(\mathrm{tr'}_M^S) = \Phi(S),$$
#! where $\mathcal{M}(S)$ is the set of maximal subgroups of $S$, and
#! $\mathrm{tr'}_M^S \colon S \to M/\Phi(M)$ is the transfer homomorphism.
#! 
#! These tests only apply at $p=2$ when $\mathrm{Aut}(S)$ is a $2$-group. 
#! It is based on <Cite Key="AOV17" Where="Lemma 2.1" />.
#1 
#! @Arguments S
DeclareAttribute("RED_TransferMaximalTest", IsPGroup);
#! @Arguments S
#! @Returns true or false
DeclareAttribute("RED_TransferFpMaximalTest", IsPGroup);

#! @BeginExampleSession
#! gap> S := SmallGroup(2^7, 903);
#! <pc group of size 128 with 7 generators>
#! gap> RED_TransferMaximalTest(S);
#! false
#! gap> RED_TransferFpMaximalTest(S);
#! true
#! @EndExampleSession 
#! @EndGroup 

#! @BeginGroup 
#! @GroupTitle Transfer test with a list
#! @Description 
#! 
#! Let $S$ be a $2$-group and $L$ be a list of (proto-essential) subgroups of $S$. 
#! The attribute `RED_TransferTest` checks that, if $\mathrm{Aut}(S)$ is a $2$-group, then
#! $$\bigcap_{M \in L} \ker(\mathrm{tr}_M^S) = S',$$
#! where $\mathrm{tr}_M^S \colon S \to M/M'$ is the transfer homomorphism. Alternatively, 
#! `RED_TransferFpTest` checks that, if $\mathrm{Aut}(S)$ is a $2$-group, then
#! $$\bigcap_{M \in L} \ker(\mathrm{tr'}_M^S) = \Phi(S),$$
#! where $\mathrm{tr'}_M^S \colon S \to M/\Phi(M)$ is the transfer homomorphism.
#! 
#! These tests only apply at $p=2$ when $\mathrm{Aut}(S)$ is a $2$-group. 
#! It is based on <Cite Key="AOV17" Where="Lemma 2.1" />.
#! 
#! @Arguments S L
DeclareOperation("RED_TransferTest", [IsPGroup, IsList]);
#! @Arguments S L
#! @Returns true or false
DeclareOperation("RED_TransferFpTest", [IsPGroup, IsList]);

#! @BeginExampleSession
#! gap> S := SmallGroup(2^7, 931);
#! <pc group of size 128 with 7 generators>
#! gap> L := AllProtoEssentials(S);
#! [ Group([ f7, f1, f2, f4, f5, f6 ]), Group([ f5, f6, f7, f1, f3, f4 ]), 
#! Group([ f5, f6, f7, f2, f3, f4 ]), Group([ f1, f2, f4, f6, f7 ]), 
#! Group([ f1, f3, f5, f6, f7 ]) ]
#! gap> RED_TransferTest(S, L{[1..3]});
#! true
#! gap> RED_TransferTest(S, L{[3..5]});
#! false
#! @EndExampleSession 

#! @EndGroup 

#! @Description 
#! 
#! Let $S$ be a $p$-group, and $L := \mathfrak{C}_0$. The function `RED_C0Test` checks that there exists some subgroup 
#! $E$ in $L$ such that $\Omega(Z(S))$ is not semi-characteristic in $E$, i.e. invariant 
#! under $O^p(O^{p'}(\mathrm{Aut}(E)))$.
#! 
#! This test applies at any prime $p$. It is based on <Cite Key="sporadics2" Where="Corollary 3.12" />.
#! 
#! @Arguments S L
#! @Returns true or false
DeclareOperation("RED_C0Test", [IsPGroup, IsList]);

#! @BeginExampleSession
#! gap> L := AllSmallGroups(3^6, A -> NilpotencyClassOfGroup(A) >= 3);;
#! gap> Length(L);
#! 360
#! gap> Number(L, S -> RED_C0Test(S, MainProtoEssentials(S, 0)));
#! 154
#! @EndExampleSession 

#! @Description 
#! 
#! Let $S$ be a $p$-group, and let $L$ be a list of proto-essential subgroups of $S$. The function `RED_CTest` checks that:
#! * $L$ has at least $2$ elements, or
#! * if $\mathrm{Aut}(S)$ is a not $2$-group, then the single subgroup in $L$ is not normal in $S$.
#! 
#! This test applies at any prime $p$. It is based on <Cite Key="AOV17" Where="Lemma 2.2(e)" />.
#! 
#! @Arguments S L
#! @Returns true or false
DeclareOperation("RED_CTest", [IsPGroup, IsList]);

#! @BeginExampleSession
#! gap> L := AllSmallGroups(3^5, A -> NilpotencyClassOfGroup(A) >= 3);;
#! gap> Length(L);
#! 32
#! gap> Number(L, S -> RED_CTest(S, AllProtoEssentials(S)));
#! 16
#! @EndExampleSession 

#! @Description 
#! 
#! Let $S$ be a $p$-group, and let $L$ be a list of proto-essential subgroups of $S$. The function 
#! `RED_SemiCharacteristicGeneratedTest` checks that the subgroup
#! $$\langle [O^p(\mathrm{Aut}(S)), S], Q_E \mid E \in L \rangle = S,$$
#! where $Q_E$ is the semi-characteristic closure of $[N_S(E), E]$ in $E$.
#! 
#! This test applies at any prime $p$. It is based on <Cite Key="AOV17" Where="Lemma 2.2(f)" />.
#! 
#! @Arguments S L
#! @Returns true or false
DeclareOperation("RED_SemiCharacteristicGeneratedTest", [IsPGroup, IsList]);

#! @BeginExampleSession
#! gap> S := SmallGroup(2^7, 931);
#! <pc group of size 128 with 7 generators>
#! gap> L := AllProtoEssentials(S);
#! [ Group([ f7, f1, f2, f4, f5, f6 ]), Group([ f5, f6, f7, f1, f3, f4 ]), 
#! Group([ f5, f6, f7, f2, f3, f4 ]), Group([ f1, f2, f4, f6, f7 ]), 
#! Group([ f1, f3, f5, f6, f7 ]) ]
#! gap> RED_SemiCharacteristicGeneratedTest(S, L{[1..3]});
#! true
#! gap> RED_SemiCharacteristicGeneratedTest(S, L{[3..5]});
#! false
#! @EndExampleSession 

#! @Description 
#! 
#! Let $S$ be a $p$-group, and let $L$ be a list of proto-essential subgroups of $S$. The function 
#! `RED_CoreTest` checks that if $N$ is a normal subgroup of $S$ 
#! such that $N$ is semi-characteristic (i.e. fixed by $O^p(O^{p'}(\mathrm{Aut}(E)))$) 
#! in each $E \in L$, then $N = 1$.
#! 
# TODO: Proof after the paper is out
#! This test applies at any prime $p$.
#! 
#! @Arguments S
#! @Returns true or false
DeclareOperation("RED_CoreTest", [IsPGroup, IsList]);

#! @BeginExampleSession
#! gap> S := SmallGroup(256, 6366);
#! <pc group of size 256 with 8 generators>
#! gap> L := AllProtoEssentials(S);
#! [ Group([ f1, f2, f4, f5, f6, f7, f8 ]), Group([ f7, f8, f3, f4, f5, f6 ]) ]
#! gap> C := List(L, CharacteristicSubgroups);;
#! gap> Intersection(C);
#! [ Group([  ]) ]
#! gap> RED_CoreTest(S, L);
#! false
#! @EndExampleSession 
