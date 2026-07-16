DeclareInfoClass("InfoFusion");

#! @Description 
#! Finds all the proto-essential subgroups of $S$, up to $\Aut(S)$-conjugacy. We make use of the algorithm given in paper2.
#! @Arguments S
#! @Returns a list
DeclareAttribute("AllProtoEssentials", IsPGroup);

#! @Description 
#! Checks whether $E$ is proto-essential in $S$. We do so by running a number of tests, given below. The algorithm avoids computing $\Aut(E)$ if possible.
#! @Arguments S E
#! @Returns true or false
DeclareOperation("IsProtoEssentialSubgroup", [IsPGroup, IsPGroup]);

#! @Description 
#! Checks whether $\Out_S(E)$ can be a Sylow $p$-subgroup of a strongly $p$-embedded subgroup. If so, we return a value specifying the type, namely:
#! * $0$ - $\Out_S(E)$ is cyclic;
#! * $1$ - $\Out_S(E)$ is elementary abelian;
#! * $2$ - Sylow $p$-subgroup of $\PSU_3(p^n)$.
#! Further tests have not been implemented yet. We further test that, if $E$ has rank $r$, then $\GL_r(p)$ is sufficiently 
#! big that it has a valid section. This is based on SAM14, Chapter 6.
#! 
#! We return $-1$ if $\Out_S(E)$ cannot be a Sylow $p$-subgroup of a strongly $p$-embedded subgroup. 
#! 
#! This test requires the computation of $N_S(E)$ but not $\Aut(E)$.
#! @Arguments S E
#! @Returns a number
DeclareOperation("PE_RankTest", [IsPGroup, IsPGroup]);

#! @Description 
#! Checks whether $E$ subgroup passes the Frattini test with respect to $S$. In particular, we check whether
#! 
#! $$C_{N_S(E)}(E/\Phi(E)) = E.$$
#! 
#! This test requires the computation of $N_S(E)$ but not $\Aut(E)$.
#! @Arguments S E
#! @Returns true or false
DeclareOperation("PE_FrattiniTest", [IsPGroup, IsPGroup]);

#! @Description 
#! Checks whether $E$ passes the lift test with respect to $S$. The value $i \geq 0$ is the one returned by `PE_RankTest'.
#! In particular, if $i > 0$, then we know that $\Out_S(E)$ is not cyclic, and 
#! by saturation, the maps in $\Out_\calF(E)$ that normalize $\Out_S(E)$ must lift to $N_S(E)$. More in paper 1, Appendix A.
#! 
#! This test requires the computation of $\Aut(N_S(E))$ (which is typically solvable) but not $\Aut(E)$.
#! @Arguments S E i
#! @Returns true or false
DeclareOperation("PE_LiftTest", [IsPGroup, IsPGroup, IsInt]);

#! @Description 
#! Checks whether $E$ passes the radical test with respect to $S$. The value $i \geq 0$ is the one returned by `PE_RankTest'.
#! In particular, we check whether
#! 
#! $$O_p(\Aut(E)) \cap \Aut_S(E) = \Inn(E).$$
#! 
#! This test requires the computation of $\Aut(E)$.
#! @Arguments S E i
#! @Returns true or false
DeclareOperation("PE_RadicalTest", [IsPGroup, IsPGroup, IsInt]);

#! @Description
#! Returns the list of the `main' proto-essential subgroups of $S$. These are precisely the ones found by the algorithm in paper2 which avoids computing all the subgroups of $S$ and iterates over some central series of $S'$. If `onlyone' is true, then only the first iteration is completed (this can detect whether the group supports corefree fusion systems). Otherwise, all iterations are run. Running `GenerateProtoEssentials`on the list $L$ returned generates all the essentials have been found.
#! @Arguments S [onlyone]
#! @Returns a list
DeclareGlobalFunction("MainProtoEssentials");

#! @Description
#! Uses the list $L$ containing the `main' proto-essential subgroups of $S$ to generate all the proto-essential subgroups of $S$.
#! @Arguments S L
#! @Returns a list
DeclareOperation("GenerateProtoEssentials", [IsPGroup, IsList]);

#! @Description 
#! Finds valid automizers for $E$ in $S$. 
#! This is not part of the proto-essentials test and forms the first step in the actual construction of fusion systems. Nonetheless, if a subgroup is proto-essential,
#! then it must have a valid automizer. This function does not construct all subgroups of $\Aut(E)/O_p(\Aut(E))$, and instead uses iterative maximal subgroup condition 
#! to do so.
#! @Arguments S E
#! @Returns a list of valid Aut_F(E)
DeclareOperation("PE_ValidAutomizers", [IsPGroup, IsPGroup]);
