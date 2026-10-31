DeclareInfoClass("InfoFusion");

#! @Chapter Proto-essential subgroups
#! @ChapterLabel ProtoEssentialSubgroups

#! @Section Brief description of the algorithm

#! Let $S$ be a finite $p$-group. Recall that $E$ is proto-essential in $S$ if there **could** exist a saturated fusion system $\mathcal{F}$ on $S$ such that $E \in \mathcal{E}(\mathcal{F})$. 

#! See Chapter <Ref Chap="Chapter_ProtoEssentialChecks" /> for the list of specific tests currently implemented.

#! In this section, we describe the algorithm for constructing all the proto-essential subgroups of $S$. This is based on <Cite Key="sporadics2" Where="Section 3"/>.

#! We fix a central series of $S$:
#! $$1 = Z_0 \leq Z_1 \leq \dots \leq Z_n = S,$$ 
#! where $|Z_i| = p^i$ for $1 \leq i \leq n$, and there exists some $1 \leq j \leq n$ such that $Z_j = S'$.
#! For $0 \leq i &lt; j$, let $\pi_i \colon S \to S/Z_i$ be the projection map, and
#! $$\mathfrak{C}_i := \{E \mid E = \pi^{-1}(C_S(x)), x \in S/Z_i \textrm{ of order } p \textrm{ with } E \textrm{ proto-essential in } S\}.$$
#! We let $\mathfrak{C} := \bigcup_{i=0}^j \mathfrak{C}_i$. In <Cite Key="sporadics2" Where="Theorem 3.6"/>, Gautam shows that if $\mathcal{F}$ is a saturated fusion system on $S$ with $E \in \mathcal{E}(\mathcal{F})$, then $E$ is $\mathcal{F}$-conjugate to some $X \in \mathfrak{C}$.

#! @Section The operations

#! @Description 
#! The attribute `AllProtoEssentials` constructs all proto-essential subgroups of a $p$-group $S$. It works as follows:
#! * it calls <Ref Func="MainProtoEssentials" /> which constructs the set $\mathfrak{C}$;
#! * it then calls <Ref Oper="GenerateProtoEssentials" Label="for IsPGroup, IsList"/>, which uses $\mathfrak{C}$ to 
#!   construct all proto-essential subgroups, switching from $\mathcal{F}$-conjugacy to $S$-conjugacy (independent of $\mathcal{F}$).
#! 
#! It should be pointed out that there is no known cases where `GenerateProtoEssentials` generates a further ($S$-conjugacy) class of proto-essential subgroups.
#! Finds all the proto-essential subgroups of $S$, up to $S$-conjugacy.
#! @Arguments S
#! @Returns a list
DeclareAttribute("AllProtoEssentials", IsPGroup);

#! @BeginExampleSession
#! gap> S := SmallGroup(3^4, 7);
#! <pc group of size 81 with 4 generators>
#! gap> L := AllProtoEssentials(S);
#! [ Group([ f4, f1, f3 ]), Group([ f4, f2, f3 ]), Group([ f1, f4 ]) ]
#! gap> List(L, StructureDescription);
#! [ "(C3 x C3) : C3", "C3 x C3 x C3", "C3 x C3" ]
#! @EndExampleSession

#! @Description
#! Returns the list of the `main` proto-essential subgroups of $S$. A proto-essential subgroup is called **main** if it lies in $\mathfrak{C}$.
#!  
#! If the second argument `i` is provided, the function behaves as follows:
#! * $i = 0$ -- we only compute $\mathfrak{C}_0$;
#! * $i = -1$ -- we only compute $\mathfrak{C} \setminus \mathfrak{C}_0$; and
#! * $i = 1$ -- we compute all $\mathfrak{C}$.
#!
#! If the argument is not provided, we compute all $\mathfrak{C}$. Running `GenerateProtoEssentials`on the list $L$ returned generates 
#! all the proto-essentials subgroups of $S$.
#! @Arguments S [i]
#! @Returns a list
DeclareGlobalFunction("MainProtoEssentials");

#! @BeginExample
#! gap> S := SmallGroup(2^7, 931);
#! <pc group of size 128 with 7 generators>
#! gap> C0 := MainProtoEssentials(S, 0);
#! [ Group([ f1, f2, f4, f6, f7 ]), Group([ f1, f3, f5, f6, f7 ]), 
#! Group([ f2, f3, f4, f5, f6, f7 ]) ]
#! gap> C := MainProtoEssentials(S, -1);
#! [ Group([ f5, f6, f7, f1, f3, f4 ]), Group([ f7, f1, f2, f4, f5, f6 ]) ]
#! @EndExample

#! @Description
#! Uses the list $L$ containing the main proto-essential subgroups of $S$ (i.e. the set $\mathfrak{C}$) to generate all the proto-essential subgroups of $S$. 
#! @Arguments S L
#! @Returns a list
DeclareOperation("GenerateProtoEssentials", [IsPGroup, IsList]);

#! @BeginExample
#! gap> S := SmallGroup(3^6, 321);
#! <pc group of size 729 with 6 generators>
#! gap> L := MainProtoEssentials(S);
#! [ Group([ f6, f2, f3, f4, f5 ]), Group([ f6, f1*f2^2, f4, f5 ]) ]
#! gap> L := GenerateProtoEssentials(S, L);
#! [ Group([ f6, f2, f3, f4, f5 ]), Group([ f6, f1*f2^2, f4, f5 ]) ]
#! @EndExample
