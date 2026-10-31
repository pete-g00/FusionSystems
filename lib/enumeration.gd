#! @Chapter Enumeration of saturated fusion systems
#! @ChapterLabel EnumerationSaturated

#! The operation <Ref Oper="AllSaturatedFusionSystems" Label="for IsPGroup"/> constructs all saturated fusion systems on a $p$-group $S$ up to
#! isomorphism, including those with $O_p(\mathcal{F}) \neq 1$ or $O^p(\mathcal{F}) \neq \mathcal{F}$. It follows
#! <Cite Key="PS_MAGMA" Where="Section 4"/>:
#! * $\textrm{Aut}_\mathcal{F}(S) = \textrm{Inn}(S) C$, where $C$ runs through the $p'$-subgroups of $\textrm{Out}(S)$ up to conjugacy;
#! * candidates for essential subgroups are representatives $E$ of the $\textrm{Aut}_\mathcal{F}(S)$-orbits of $S$-centric, non-cyclic proper
#!   subgroups with $|N_S(E)|$ maximal and $\textrm{Aut}_S(E) \cap O_p(\textrm{Aut}(E)) = \textrm{Inn}(E)$;
#! * candidates for $\textrm{Aut}_\mathcal{F}(E)$ are the subgroups $X$ of $\textrm{Aut}(E)$ containing $\textrm{Inn}(E)$ such that $Y = X/\textrm{Inn}(E)$
#!   has the Sylow $p$-subgroup $\textrm{Out}_S(E)$, contains the restrictions of $\textrm{Aut}_\mathcal{F}(S)$, satisfies $O_p(Y) = 1$ and has a strongly
#!   $p$-embedded subgroup; if $N_S(E) = S$, then $N_Y(\textrm{Out}_S(E))$ consists of restrictions of $\textrm{Aut}_\mathcal{F}(S)$;
#! * every set of candidate essential subgroups with every choice of automizers is tested with <Ref Prop="IsSaturatedFusionSystem" Label="for IsFusionSystem"/>,
#!   and isomorphic copies are removed with <Ref Oper="IsomorphismFusionSystems" Label="for IsFusionSystem, IsFusionSystem"/>.
#!
#! No restriction on $O_p(\mathcal{F})$ or $O^p(\mathcal{F})$ is made. The search is exhaustive without the further pruning of
#! <Cite Key="PS_MAGMA"/>, so it is only practical for small groups.

#! @Description
#! Returns a list of all saturated fusion systems on the $p$-group $S$ up to isomorphism.
#! @Arguments S
#! @Returns a list of fusion systems
DeclareOperation("AllSaturatedFusionSystems", [IsPGroup]);

#! @Description
#! Returns a list of all subgroups $X \leq \textrm{Aut}(E)$ which are candidates for $\textrm{Aut}_\mathcal{F}(E)$ for an $\mathcal{F}$-essential subgroup $E$ of
#! $S$ in a saturated fusion system $\mathcal{F}$ with $\textrm{Aut}_\mathcal{F}(S) = \langle \textrm{Inn}(S), AS \rangle$ (see above).
#! @Arguments S, E, AS
#! @Returns a list of groups of automorphisms
DeclareOperation("EssentialAutomizerCandidates", [IsPGroup, IsPGroup, IsList]);
