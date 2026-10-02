#! @Chapter Checks for proto-essentials 
#! @ChapterLabel ProtoEssentialChecks

#! @Section Introduction
#! In this chapter, we describe all the tests currently implemented in GAP that test whether a subgroup $E$ of a $p$-group $S$ is proto-essential. Recall that $E$ is proto-essential in $S$ if there **could** exist a saturated fusion system $\mathcal{F}$ on $S$ such that $E \in \mathcal{E}(\mathcal{F})$.

#! The tests are vastly different depending on the prime $p$. If $p=2$, then the tests are based on the tests in Andersen, Oliver and Ventura in <Cite Key="AOV" Where="Proposition 2.3"/>. At $p$ odd, we make use of the tests given by Parker-Semeraro in <Cite Key="PS-MAGMA" /> and <Cite Key="sporadics1" Where="Appendix A"/>.
 
#! @Section General Tests

#! These are tests that apply for any prime $p$.

#! @Description 
#! Checks whether $\textrm{Out}_S(E)$ can be a Sylow $p$-subgroup of a strongly $p$-embedded subgroup. If so, we return a value specifying the type, namely:
#! * $0$ - $\textrm{Out}_S(E)$ is cyclic;
#! * $1$ - $\textrm{Out}_S(E)$ is elementary abelian;
#! * $2$ - Sylow $p$-subgroup of $\textrm{PSU}_3(p^n)$.
#! Further tests have not been implemented yet. We further test that, if $E$ has rank $r$, then $\textrm{GL}_r(p)$ is sufficiently 
#! big that it has a valid section. This is based on SAM14, Chapter 6.
#! 
#! We return $-1$ if $\textrm{Out}_S(E)$ cannot be a Sylow $p$-subgroup of a strongly $p$-embedded subgroup. 
#! 
#! This test requires the computation of $N_S(E)$ but not $\textrm{Aut}(E)$.
#! @Arguments S E
#! @Returns a number
DeclareOperation("PE_RankTest", [IsPGroup, IsPGroup]);

#! @Description 
#! Checks whether $E$ subgroup passes the Frattini test with respect to $S$. In particular, we check whether
#! 
#! $$C_{N_S(E)}(E/\Phi(E)) = E.$$
#! 
#! This test requires the computation of $N_S(E)$ but not $\textrm{Aut}(E)$.
#! @Arguments S E
#! @Returns true or false
DeclareOperation("PE_FrattiniTest", [IsPGroup, IsPGroup]);

#! @Description 
#! Checks whether $E$ passes the lift test with respect to $S$. The value $i \geq 0$ is the one returned by `PE_RankTest`.
#! In particular, if $i > 0$, then we know that $\textrm{Out}_S(E)$ is not cyclic, and 
#! by saturation, the maps in $\textrm{Out}_{\mathcal{F}}(E)$ that normalize $\textrm{Out}_S(E)$ must lift to $N_S(E)$. More in paper 1, Appendix A.
#! 
#! This test requires the computation of $\textrm{Aut}(N_S(E))$ (which is typically solvable) but not $\textrm{Aut}(E)$.
#! @Arguments S E i
#! @Returns true or false
DeclareOperation("PE_LiftTest", [IsPGroup, IsPGroup, IsInt]);

#! @Description 
#! Checks whether $E$ passes the radical test with respect to $S$. The value $i \geq 0$ is the one returned by `PE_RankTest`.
#! In particular, we check whether
#! 
#! $$O_p(\textrm{Aut}(E)) \cap \textrm{Aut}_S(E) = \textrm{Inn}(E).$$
#! 
#! This test requires the computation of $\textrm{Aut}(E)$.
#! @Arguments S E i
#! @Returns true or false
DeclareOperation("PE_RadicalTest", [IsPGroup, IsPGroup, IsInt]);

#! @Description 
#! Checks whether $E$ passes the involution conjugate test with respect to $S$. The value $i \geq 0$ is the one returned by `PE_RankTest`.
#! In particular, if $p=2$ and $i>0$, we check that all involutions in $\textrm{Out}_S(E)$ are conjugate in $N_{\textrm{Out}(E)}(\textrm{Out}_S(E))$.
#! This test requires the computation of $\textrm{Aut}(E)$.
#! @Arguments S E i
#! @Returns true or false
DeclareOperation("PE_InvolutionsConjugate", [IsPGroup, IsPGroup, IsInt]);
