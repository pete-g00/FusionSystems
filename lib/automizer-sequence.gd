#! @Chapter Automizer Sequences
#! @ChapterLabel AutomizerSequences

#! 
#! Let $S$ be a $p$-group, with proto-essential subgroups $E_1, \dots, E_n$. An **automizer sequence** is a list $P := [H_{i_1}, \dots, H_{i_k}]$, where $H_{i_j} \leq \textrm{Aut}(E_{i_j})$ is a valid automizer for $E_{i_j}$ in $S$. 
#! In other words, $\textrm{Aut}_S(E_{i_j})$ is a Sylow $p$-subgroup of $H_{i_j})$, and $H_{i_j}/\textrm{Inn}(E_{i_j})$ contains a strongly $p$-embedded subgroup. Note that we do not include a choice of $H_S \leq \textrm{Aut}(S)$ here.

#! These are prototypes for saturated fusion systems. In this chapter, we describe processes to determine many important properties about automizer sequences that will allow us to determine whether the corresponding fusion system would be reduced. Note that the functionalities here are not guaranteed to be correct or complete just yet.

#! @Section The functions

# TODO: Explain the tests involved here already(?) At least the general process.

#! @Description
#! Let $S$ be a $p$-group, and let $L$ be a list of subgroups of $S$, all of which are proto-essential in $S$. We compute all possible automizer sequences involving the subgroups in $L$ that could lead to reduced fusion systems.
#! @Arguments S L
#! @Returns a list of valid Aut_F(E)
DeclareOperation("FindReducedSequences", [IsPGroup, IsList]);

#! @Description
#! Given two automizer sequences $P_1$ and $P_2$, check whether there exists some $\phi \in \textrm{Aut}(S)$ such that $P_1^\phi = P_2$. This computation mimics isomorphism of fusion systems. The action of $\phi$ is dependent of the ordering of the $P_i$'s.
#! @Arguments S P1 P2
#! @Returns an isomorphism mapping
DeclareOperation("IsomorphismSequences", [IsPGroup, IsList, IsList]);

#! @Description 
#! Finds valid automizers for $E$ in $S$. 
#! This is not part of the proto-essentials test and forms the first step in the actual construction of fusion systems. Nonetheless, if a subgroup is proto-essential,
#! then it must have a valid automizer. This function does not construct all subgroups of $\textrm{Aut}(E)/O_p(\textrm{Aut}(E))$, and instead uses iterative maximal subgroup condition 
#! to do so.
#! @Arguments S E
#! @Returns a list
DeclareOperation("PE_ValidAutomizers", [IsPGroup, IsPGroup]);

#! @Description
#! Let $S$ be a $p$-group, and let $E &lt; S$ with some fixed $H_E \leq \textrm{Aut}(E)$ part of an automizer sequence. The operation `FindSmallestBorel` computes the subgroup of $\textrm{Aut}(S)$ consisting of extensions from $N_{H_E}(\textrm{Aut}_S(E))$. If not every map in the normalizer subgroup exists, we return `fail`.
#! @Arguments S AutFE
#! @Returns a group
DeclareOperation("FindSmallestBorel", [IsPGroup, IsGroupOfAutomorphismsFiniteGroup]);

#! @Description
#! Let $S$ be a $p$-group, and let $E &lt; S$ with some fixed $H_E \leq \textrm{Aut}(E)$ part of an automizer sequence. Let $H_S \leq \textrm{Aut}(S)$ be a subgroup. The operation `IsAutomizerBorelCompatible` checks whether the restrictions of $H_S$ are **compatible** with $H_E$. In particular, if $A_0 \leq \textrm{Aut}(E)$ consists of restrictions from $H_S$, we have that 
#! $$O^{p'}(\langle A_0, H_E \rangle) = H_E.$$
#! @Arguments S AutFS AutFE
#! @Returns true or false
DeclareOperation("IsAutomizerBorelCompatible", [IsPGroup, IsGroupOfAutomorphismsFiniteGroup, IsGroupOfAutomorphismsFiniteGroup]);

# This function is not yet ready
DeclareOperation("IsFocalCompatibleSequence", [IsPGroup, IsGroupOfAutomorphismsFiniteGroup, IsList]);

#! @Description
#! Let $S$ be a $p$-group and let $P$ be an automizer sequence. The operation `IsCompatibleSequence` checks whether $P$ can lead to a saturated fusion system. Note that there can be false positives -- $P$ may not lead to a saturated fusion system (based on the analysis of centric, radical subgroups) but passes this test.
#! @Arguments S P
#! @Returns true or false
DeclareOperation("IsCompatibleSequence", [IsPGroup, IsList]);

#! @Description
#! Let $S$ be a $p$-group and let $P$ be an automizer sequence. If we set $\mathcal{F} := \langle P \rangle$,
#! the operation `OrbitStabilizerFusion` returns a record `R`, storing:
#! * $\mathcal{F}$-orbit $A^{\mathcal{F}}$ (in `R.orbit`),
#! * the isomorphisms $\phi_i \colon A \to A_i$ for some $A_i \in A^{\mathcal{F}}$ (in `R.maps`), and
#! * the automizer $\mathrm{Aut}_{\mathcal{F}}(A)$ (in `R.AutFA`).
#! The operation uses breadth-first search, where the vertices is the $\mathcal{F}$-orbit and the edges are the maps in $P$.
#! @Arguments S A P
#! @Returns a record
DeclareOperation("OrbitStabilizerFusion", [IsPGroup, IsPGroup, IsList]);

#! @Description
#! Let $S$ be a $p$-group, $W$ be a subgroup of $S$, and let $P$ be an automizer sequence. The operation `WeakRadicalCheck` 
#! does a weaker version of the saturation check with respect to the possible centric-radical subgroup $W$. In particular, 
#! taking $\mathcal{F} := \langle P \rangle$, the function works as follows:
#! * We start by computing the orbit $W^\mathcal{F}$ and the stabilizer $\mathrm{Aut}_{\mathcal{F}}(W)$.
#! * We conjugate $W$ so that it is fully $\mathcal{F}$-normalized.
#! * We check that $\mathrm{Aut}_S(W)$ is a Sylow $p$-subgroup of $\mathrm{Aut}_{\mathcal{F}}(W)$.
#! * If $X$ is a subgroup of $N_S(W)$ such that $N_{\mathrm{Out}_{\mathcal{F}}(W)}(\mathrm{Out}_X(W))/\mathrm{Out}_X(W)$ has a strongly $p$-embedded subgroup, then
#! $$N_{\mathrm{Aut}_{\mathcal{F}}(W)}(\mathrm{Aut}_X(W)) = \mathrm{Aut}_{\mathrm{Aut}_{\mathcal{F}}(W)}(\mathrm{Aut}_X(W)).$$
#! The function always returns true if $W$ is not $\mathcal{F}$-centric or if there exists a $\mathcal{F}$-conjugate $A$ 
#! of $W$ satisfying:
#! $$O_p(\mathrm{Aut}_{\mathcal{F}}(A))) \cap \mathrm{Aut}_S(E) > \mathrm{Inn}(E).$$
#! @Arguments S W P
#! @Returns true or false
DeclareOperation("WeakRadicalCheck", [IsPGroup, IsPGroup, IsList]);
