#! @Chapter Checks for proto-essentials 
#! @ChapterLabel ProtoEssentialChecks

#! In this chapter, we describe all the tests currently implemented in GAP that test whether
#! a subgroup $E$ of a $p$-group $S$ is proto-essential. Recall that $E$ is proto-essential 
#! in $S$ if there **could** exist a saturated fusion system $\mathcal{F}$ on $S$ such that 
#! $E \in \mathcal{E}(\mathcal{F})$.

#! @Section The main functions

#! @Description 
#!
#! Let $S$ be a $p$-group and $E$ be a subgroup of $S$. The operation `IsProtoEssential` checks whether
#! $E$ is a proto-essential subgroup of $S$. 
#! 
#! This function checks whether the group $E$ satisfies certain properties with respect to $S$ that are known to hold
#! when $E$ is an essential subgroup in some fusion system $\mathcal{F}$ on $E$. In this process, we construct (in order):
#! * $C_S(E)$;
#! * $N_S(E)$;
#! * $\mathrm{Aut}(N_S(E))$; and
#! * $\mathrm{Aut}(E)$.
#! 
#! Each computation is considered more expensive than the previous one.
#! See Section <Ref Sect="Section_PEChecks"/> for the list of tests currently implemented.
#! 
#! Note that it is possible that $E$ is found to be proto-essential even though there is no fusion system $\mathcal{F}$ on $S$
#! with $E \in \mathcal{E}(\mathcal{F})$. This can be for various reasons, for example, $E$ could be essential in $\mathcal{F}$
#! only if there is an overgroup of $E$ that is also essential, but there is no such group. Some of these cases may be ruled
#! out using automizer sequences, but it cannot be fully determined without constructing the actual fusion systems.
#! 
#! @Arguments S E
#! @Returns true or false
DeclareOperation("IsProtoEssential", [IsPGroup, IsPGroup]);

#! @BeginExampleSession
#! gap> S := SmallGroup(3^4, 7);
#! <pc group of size 81 with 4 generators>
#! gap> C := SubgroupsSolvableGroup(S);;
#! gap> C := Filtered(C, A -> IsProtoEssential(S, A));
#! [ Group([ f3, f4, f1 ]), Group([ f1, f4 ]), Group([ f3, f4, f2 ]) ]
#! gap> List(C, StructureDescription);
#! [ "(C3 x C3) : C3", "C3 x C3", "C3 x C3 x C3" ]
#! @EndExampleSession 

#! @Description 
#! 
#! The operation `IsProtoEssentialNC` behaves like `IsProtoEssential`, but further assumes that:
#! * $E$ is a proper subgroup of $S$;
#! * $C_S(E) \leq E$;
#! * $E$ passes `Zed0Test`.
#!
#! @Arguments S E
#! @Returns true or false
DeclareOperation("IsProtoEssentialNC", [IsPGroup, IsPGroup]);

#! @Section The specific functions
#! @SectionLabel PEChecks

#! @Description 
#! 
#! Let $S$ be a $p$-group. The attribute `Zed0` computes the subgroup $Z_0$ of $S$, which is given by:
#! $$Z_0 := \langle x \in Z_2(S) \mid |[S, x]| \leq p \rangle.$$
#!  
#! @Arguments S
#! @Returns a subgroup
DeclareAttribute("Zed0", IsPGroup);

# TODO: Odd proof after the paper is out
#! @Description 
#! 
#! Let $S$ be a $p$-group and $E$ be a subgroup of $S$. The operation `Zed0Test` checks that one of the following holds:
#! * $Z_0 \leq E$; or
#! * $[N_S(E) : E] = p$, and there exists some $x \in \Omega(Z(E))$ such that $E = C_S(x)$.
#!
#! Note that this function is not used when constructing $\mathfrak{C}$ as the choice of $x$ is easier to find while 
#! the set $\mathfrak{C}_0$ is being constructed.
#!
#! This test applies at any prime $p$. It is based on <Cite Key="AOV17" Where="Proposition 2.3(a)" /> (proven for $p=2$).
#!
#! @Arguments S E
#! @Returns true or false
DeclareOperation("Zed0Test", [IsPGroup, IsPGroup]);

#! @BeginExampleSession
#! gap> S := SmallGroup(2^7, 931);
#! <pc group of size 128 with 7 generators>
#! gap> Z0 := Zed0(S);
#! Group([ f6, f7 ])
#! gap> C := SubgroupsSolvableGroup(S);;
#! gap> Length(C);
#! 135
#! gap> Number(C, A -> Zed0Test(S,A));
#! 66
#! @EndExampleSession 

#! @Description 
#!
#! Let $S$ be a $p$-group and $E$ be a subgroup of $S$. The operation `RankTest` checks that $\textrm{Out}_S(E)$ 
#! is isomorphic to  a Sylow $p$-subgroup of a group containing a strongly $p$-embedded subgroup. If so, we return 
#! a value specifying its type, namely:
#! * $0$ -- $\textrm{Out}_S(E)$ is cyclic or quaternion;
#! * $1$ -- $\textrm{Out}_S(E)$ is elementary abelian of order $\geq p^2$;
#! * $2$ -- Sylow $p$-subgroup of $\textrm{PSU}_3(p^n)$;
#! * $3$ -- Sylow $2$-subgroup of $\mathrm{Sz}(2^{2n+1})$;
#! * $4$ -- Sylow $3$-subgroup of ${^2\mathrm{G}}_2(3^{2n+1})$; and
#! * $5$ -- $3^{1+2}_-$ and $5^{1+2}_-$.
#! We return $-1$ if none of the cases above apply. During the process, we also check that the subgroup $E$ has
#! sufficiently high rank to ensure that $\mathrm{Aut}(E)$ has a possible valid section.
#!
#! This test applies at any prime $p$. It is based on <Cite Key="SAM14" Where="Proposition 6.9" />.
#!  
#! @Arguments S E
#! @Returns a number
DeclareOperation("RankTest", [IsPGroup, IsPGroup]);

#! @BeginExampleSession
#! gap> S := SmallGroup(3^6, 479);
#! <pc group of size 729 with 6 generators>
#! gap> A := First(MaximalSubgroups(S), IsElementaryAbelian);
#! Group([ f2, f3, f4, f5, f6 ])
#! gap> B := First(MaximalSubgroups(S), A -> Exponent(A) = 3 
#! >               and not IsElementaryAbelian(A));
#! Group([ f1, f3, f4, f5, f6 ])
#! gap> C := First(MaximalSubgroups(S), A -> Exponent(A) = 9);
#! Group([ f1, f2, f3, f5, f6 ])
#! gap> T := Intersection(A, B);
#! Group([ f3^2, f4^2, f5^2, f6^2 ])
#! gap> U := Intersection(A, B, C);
#! Group([ f3^2, f5^2, f6^2 ])
#! gap> RankTest(S, A);
#! 0
#! gap> RankTest(S, B);
#! 0
#! gap> RankTest(S, C);
#! 0
#! gap> RankTest(S, T);
#! 1
#! gap> RankTest(S, U);
#! -1
#! @EndExampleSession

# TODO: Does this apply at $p$ odd? If not, is there something that can apply here?

#! @Description 
#!
#! Let $S$ be a $2$-group and $E$ be a subgroup of $S$. The operation `ModuleTest` checks that, if $\mathrm{Out}_S(E)$ has 
#! order $2^k$ (for $k \geq 2$), then for all $x \in \mathrm{Out}_S(E)$, if $x \neq 1$, then $[x, E/\Phi(E)]$ is not cyclic.
#!
#! This test applies at $p=2$. It is based on <Cite Key="OV" Where="Proposition 3.3(c)" />.
#!  
#! @Arguments S E
#! @Returns true or false
DeclareOperation("ModuleTest", [IsPGroup, IsPGroup]);

#! @BeginExampleSession
#! gap> S := SmallGroup(2^7, 931);
#! <pc group of size 128 with 7 generators>
#! gap> C := SubgroupsSolvableGroup(S);;
#! gap> Length(C);
#! 135
#! gap> Number(C, A -> Zed0Test(S,A) and ModuleTest(S,A));
#! 24
#! @EndExampleSession 

# TODO: Change this? Compare with the BL version of this code. Certainly check also wrt. $Z(E)$
# TODO: Do the $Z(S)$/$Z_2(S)$ version here as well?

#! @Description 
#! 
#! Let $S$ be a $p$-group and $E$ be a subgroup of $S$. The operation `FrattiniTest` checks that
#! $$C_{N_S(E)}(E/\Phi(E)) = E.$$
#! 
#! This test applies at any prime $p$. It is based on <Cite Key="sporadics1" Where="Appendix A" />.
#! 
#! @Arguments S E
#! @Returns true or false
DeclareOperation("FrattiniTest", [IsPGroup, IsPGroup]);

#! @BeginExampleSession
#! gap> S := SmallGroup(3^4, 7);
#! <pc group of size 81 with 4 generators>
#! gap> A := First(MaximalSubgroups(S), A -> IsElementaryAbelian(A));
#! Group([ f2, f3, f4 ])
#! gap> B := First(MaximalSubgroups(S), A -> Exponent(A) = 3 
#! >               and not IsElementaryAbelian(A));
#! Group([ f1, f3, f4 ])
#! gap> C := First(MaximalSubgroups(S), A -> Exponent(A) = 9);
#! Group([ f1*f2^2, f3, f4 ])
#! gap> T := Intersection(A, B);
#! Group([ f3^2, f4^2 ])
#! gap> FrattiniTest(S, A);
#! true
#! gap> FrattiniTest(S, B);
#! true
#! gap> FrattiniTest(S, C);
#! true
#! gap> FrattiniTest(S, T);
#! false
#! @EndExampleSession 

# Value   | Description                   | $a$
# ----------------------------------------------------------------------------------------------------------
# $0$     | Cyclic or quaternion          | $-$ 
# $1$     | Elementary abelian            | $\frac{1}{(2, p-1)} (p^n-1)$ OR $(p-1)^2$ ($p \geq 5$, $n = 2$) 
# $2$     | $\PSU_3(p^n)$                 | $\frac{1}{(3,p-1)}(p^2-1)$ 
# $3$     | $\mathrm{Sz}(2^{2n+1})$       | $2^{2n+1}-1$ 
# $4$     | ${^2\mathrm{G}}_2(3^{2n+1})$  | $3^{2n+1}-1$ 
# $5$     | $3^{1+2}_-, 5^{1+2}_-$        | $p-1$ 

#! @Description 
#!
#! Let $S$ be a $p$-group, $E$ be a subgroup of $S$ of type $i$ (see <Ref Oper="RankTest" Label="for IsPGroup, IsPGroup"/>).
#! The operation `LiftTest` checks 
#! whether the maps in $N_{\mathrm{Out}_{\mathcal{F}}(E)}(\mathrm{Out}_S(E))$ are present as expected. In particular,
#! there is some value $a$ known to divide $N_{\mathrm{Out}_{\mathcal{F}}(E)}(\mathrm{Out}_S(E))$ for each choice of $i$.
#! We check that $a$ divides:
#! * $|\mathrm{Aut}(N_S(E))|$;
#! * $|N_{\mathrm{Aut}(E)}(\mathrm{Aut}_S(E))|$; and
#! * $|N_{\mathrm{Out}(E)}(\mathrm{Out}_S(E)) : C_{\mathrm{Out}(E)}(\mathrm{Out}_S(E))|$.
#!
#! This test applies at any prime $p$. It is based on <Cite Key="sporadics1" Where="Lemma A.1" /> and <Cite Key="OV" Where="Proposition 3.3(b)" />.
#! 
#! @Arguments S E i
#! @Returns true or false
DeclareOperation("LiftTest", [IsPGroup, IsPGroup, IsInt]);

#! @BeginExampleSession
#! gap> S := SmallGroup(3^6, 479);
#! <pc group of size 729 with 6 generators>
#! gap> A := First(MaximalSubgroups(S), IsElementaryAbelian);
#! Group([ f2, f3, f4, f5, f6 ])
#! gap> B := First(MaximalSubgroups(S), A -> Exponent(A) = 3 
#! >               and not IsElementaryAbelian(A));
#! Group([ f1, f3, f4, f5, f6 ])
#! gap> C := First(MaximalSubgroups(S), A -> Exponent(A) = 9);
#! Group([ f1, f2, f3, f5, f6 ])
#! gap> T := Intersection(A, B);
#! Group([ f3^2, f4^2, f5^2, f6^2 ])
#! gap> LiftTest(S, A, 0);
#! true
#! gap> LiftTest(S, B, 0);
#! true
#! gap> LiftTest(S, C, 0);
#! true
#! gap> LiftTest(S, T, 1);
#! false
#! @EndExampleSession

#! @Description 
#!
#! Let $S$ be a $p$-group, $E$ be a subgroup of $S$ of type $i$ (see <Ref Oper="RankTest" Label="for IsPGroup, IsPGroup"/>).
#!  The operation `ValidAutTest` checks
#! whether there is a valid section of $\mathrm{Aut}(E)$ that contains the expected $\mathrm{Aut}_{\mathcal{F}}(E)$.
#! Note that this check is up to (order of) composition factors, and does not imply that the expected section actually
#! exists inside $\mathrm{Aut}(E)$.
#! 
#! This test applies at any prime $p$. It is based on <Cite Key="SAM14" Where="Proposition 6.9" /> and
#! <Cite Key="PS_MAGMA" Where="Proposition 4.5" />.
#! 
#! @Arguments S E i
#! @Returns true or false
DeclareOperation("ValidAutTest", [IsPGroup, IsPGroup, IsInt]);

#! @BeginExampleSession
#! gap> S := SmallGroup(3^4, 7);
#! <pc group of size 81 with 4 generators>
#! gap> A := First(MaximalSubgroups(S), A -> IsElementaryAbelian(A));
#! Group([ f2, f3, f4 ])
#! gap> B := First(MaximalSubgroups(S), A -> Exponent(A) = 3 
#! >               and not IsElementaryAbelian(A));
#! Group([ f1, f3, f4 ])
#! gap> C := First(MaximalSubgroups(S), A -> Exponent(A) = 9);
#! Group([ f1*f2^2, f3, f4 ])
#! gap> ValidAutTest(S, A, 0);
#! true
#! gap> ValidAutTest(S, B, 0);
#! true
#! gap> ValidAutTest(S, C, 0);
#! false
#! @EndExampleSession 

#! @Description 
#! 
#! Let $S$ be a $p$-group, $E$ be a proto-essential subgroup. The operation `RadicalTest`checks
#! whether
#! 
#! $$|O_p(\textrm{Aut}(E)) \cap \textrm{Aut}_S(E)| = [E : Z(E)].$$
#! 
#! This test applies at any prime $p$. It is based on <Cite Key="PS_MAGMA" Where="Proposition 4.8(2)" />.
#! 
#! @Arguments S E
#! @Returns true or false
DeclareOperation("RadicalTest", [IsPGroup, IsPGroup]);

#! @BeginExampleSession
#! gap> S := SmallGroup(3^4, 7);
#! <pc group of size 81 with 4 generators>
#! gap> A := First(MaximalSubgroups(S), A -> IsElementaryAbelian(A));
#! Group([ f2, f3, f4 ])
#! gap> B := First(MaximalSubgroups(S), A -> 
#! >               Exponent(A) = 3 and not IsElementaryAbelian(A));
#! Group([ f1, f3, f4 ])
#! gap> C := First(MaximalSubgroups(S), A -> Exponent(A) = 9);
#! Group([ f1*f2^2, f3, f4 ])
#! gap> RadicalTest(S, A);
#! true
#! gap> RadicalTest(S, B);
#! true
#! gap> RadicalTest(S, C);
#! false
#! @EndExampleSession 
