DeclareInfoClass("InfoFusion");

#! @Chapter Proto-essential subgroups
#! @ChapterLabel ProtoEssentialSubgroups

#! @Section Brief description of the algorithm

#! Let $S$ be a finite $p$-group. Recall that $E$ is proto-essential in $S$ if there **could** exist a saturated fusion system $\mathcal{F}$ on $S$ such that $E \in \mathcal{E}(\mathcal{F})$. See Chapter <Ref Chap="Chapter_ProtoEssentialChecks" /> on the proto-essential tests.

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
#! * it calls the function `AllProtoEssentials` which constructs the set $\mathfrak{C}$;
#! * it then calls `GenerateProtoEssentials`, which uses $\mathfrak{C}$ to construct all proto-essential subgroups, switching from $\mathcal{F}$-conjugacy to $S$-conjugacy (independent of $\mathcal{F}$).
#! 
#! It should be pointed out that there is no known cases where `GenerateProtoEssentials` generates a further ($S$-conjugacy) class of proto-essential subgroups.
#! Finds all the proto-essential subgroups of $S$, up to $S$-conjugacy.
#! @Arguments S
#! @Returns a list
DeclareAttribute("AllProtoEssentials", IsPGroup);

#! @Description
#! Returns the list of the `main` proto-essential subgroups of $S$. A proto-essential subgroup is called **main** if it lies in $\mathfrak{C}$.
#!  
#! If `onlyOne` is true, then we only compute $\mathfrak{C}_0$. Otherwise, all iterations are run.
#! Running `GenerateProtoEssentials`on the list $L$ returned generates all the proto-essentials subgroups of $S$.
#! @Arguments S [onlyOne]
#! @Returns a list
DeclareGlobalFunction("MainProtoEssentials");

#! @Description
#! Uses the list $L$ containing the main proto-essential subgroups of $S$ (i.e. the set $\mathfrak{C}$) to generate all the proto-essential subgroups of $S$. 
#! @Arguments S L
#! @Returns a list
DeclareOperation("GenerateProtoEssentials", [IsPGroup, IsList]);

#! @Description 
#! The operation `IsProtoEssential` checks whether a subgroup $E$ is proto-essential in $S$. This is a list of (non-exhaustive) tests that remove a subgroup being proto-essential. See Chapter <Ref Label="Chapter_ProtoEssentialChecks" /> for the tests.
#! @Arguments S E
#! @Returns true or false
DeclareOperation("IsProtoEssential", [IsPGroup, IsPGroup]);
