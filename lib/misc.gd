#! @Chapter Other functions

#! @Section Group actions

#! @Description 
#!
#! Let $G$ be a finite group, and $A$ be a normal subgroup in $U$. Let $q \colon G \to G/A$. The function 
#! `OnQuotient(q)` returns a function, such that for $t \in G/A$ and $x \in G$, `OnQuotient(q)(t, x)` 
#! returns $q(xhx^{-1})$, where $h \in G$ satisfies $q(h) = t$.
#!  
#! @Arguments q
#! @Returns a function
DeclareGlobalFunction("OnQuotient");

#! @Description 
#!
#! Let $G$ be a finite group, with subgroups $B \leq A \leq G$, with $B$ normal in $G$. The function 
#! `CentralizerMod(S, A, B)` returns the subgroup $C_G(A/B)$, given by:
#!
#! $$C_G(A/B) := \langle x \in G \mid [A, x] \leq B \rangle.$$
#!  
#! @Arguments G A B
#! @Returns a subgroup of G
DeclareOperation("CentralizerMod", [IsGroup, IsGroup, IsGroup]);

#! @BeginExampleSession
#! gap> S := SmallGroup(5^6, 643);
#! <pc group of size 15625 with 6 generators>
#! gap> U := UpperCentralSeries(S);
#! [ Group([ a6, a5, a4, a3, a1, a2 ]), Group([ a6, a5, a4, a3 ]), 
#! Group([ a6, a5, a4 ]), Group([ a6, a5 ]), Group([ a6 ]), Group([  ]) ]
#! gap> R := CentralizerMod(S, U[4], U[6]);
#! Group([ <identity> of ..., a2, a3, a4, a5, a6 ])
#! gap> R = Centralizer(S, U[4]);
#! true
#! gap> A := CentralizerMod(S, U[3], U[5]);
#! Group([ a1, <identity> of ..., a3, a4, a5, a6 ])
#! gap> A = R;
#! false
#! @EndExampleSession

#! @Description 
#!
#! Let $\phi$ be a map and let $x$ be either an element or a subset of the domain of $\phi$. 
#! The function `OnImage(x, phi)` returns $\phi(x)$.
#! 
#! @Arguments x phi
#! @Returns an element or a subset
DeclareGlobalFunction("OnImage");

#! @Description 
#!
#! Let $G$ be a group and $n$ a nice monomorphism for (a subgroup of) $\mathrm{Aut}(G)$, with image $A$.
#! The function `OnImageNM(n)` returns a function such that, for some element $\phi \in A$ and
#! an element (or a subgroup) $x$ of $G$, `OnImageNM(n)(x, phi)` return $\hat{\phi}(x)$, where 
#! $\hat{\phi} \in \mathrm{Aut}(G)$ is the preimage of $\phi$ with respect to the injective map $n$.
#! 
#! @Arguments n
#! @Returns a function
DeclareGlobalFunction("OnImageNM");

#! @BeginExampleSession
#! gap> S := SmallGroup(5^6, 642);
#! <pc group of size 15625 with 6 generators>
#! gap> AutS := AutomorphismGroup(S);
#! <group of size 1562500 with 10 generators>
#! gap> n := NiceMonomorphism(AutS);
#! <action isomorphism>
#! gap> AutS := n(AutS);
#! <permutation group of size 1562500 with 10 generators>
#! gap> V := Group(S.2, S.6);
#! <pc group with 2 generators>
#! gap> A := Stabilizer(AutS, V, OnImageNM(n));
#! <permutation group of size 12500 with 7 generators>
#! @EndExampleSession

#! @Description 
#!
#! Let $\phi$ be a map and let $L$ be a list of elements in the domain of $\phi$. 
#! The function `OnImageTuples(L, x)` returns a list containing $\phi(x)$ for each $x \in L$, 
#! while maintaining the order.
#! 
#! @Arguments L x
#! @Returns a list
DeclareGlobalFunction("OnImageTuples");

#! @Description 
#!
#! Let $G$ be a group and $n$ a nice monomorphism for (a subgroup of) $\mathrm{Aut}(G)$, with image $A$.
#! The function `OnImageTuplesNM(n)` returns a function such that, for some element $\phi \in A$ and
#! a list $L$ of elements in $G$, `OnImageTuplesNM(n)(L, phi)` return a list of elements $\hat{\phi}(x)$, 
#! where $x \in L$ and $\hat{\phi} \in \mathrm{Aut}(G)$ is the preimage of $\phi$ with 
#! respect to the injective map $n$.
#! 
#! @Arguments S A
#! @Returns a function
DeclareGlobalFunction("OnImageTuplesNM");

#! @Section Group automorphisms

#! @BeginGroup 
#! @Description 
#!
#! Let $G$ and $H$ be subgroups of some finite group. The group `Automizer(G, H)` is the automizer subgroup
#! $\mathrm{Aut}_G(H)$, given by:
#!
#! $$\mathrm{Aut}_G(H) := \langle c_g \mid g \in N_G(H) \rangle,$$
#!
#! where $c_g \colon H \to H$ is the conjugation automorphism. It is a subgroup of $\mathrm{Aut}(A)$.
#! 
#! @Arguments G H
#! @Returns a subgroup of Aut(H)
DeclareOperation("Automizer", [IsGroup, IsGroup]);
#! @Arguments A H
DeclareOperation("Automizer", [IsGroupOfAutomorphismsFiniteGroup, IsGroup and IsFinite]);

#! @BeginExampleSession
#! gap> G := AlternatingGroup(6);
#! Alt( [ 1 .. 6 ] )
#! gap> S := SylowSubgroup(G, 2);
#! Group([ (1,2)(3,4), (1,3)(2,4), (1,2)(5,6) ])
#! gap> M := MaximalSubgroups(S);
#! [ Group([ (3,4)(5,6), (1,2)(3,4) ]), Group([ (1,3)(2,4), (1,2)(3,4) ]), 
#! Group([ (1,3,2,4)(5,6), (1,2)(3,4) ]) ]
#! gap> AutGM := List(M, A -> Automizer(G, A));
#! [ <group with 2 generators>, <group with 2 generators>, <group with 2 generators> ]
#! gap> List(AutGM, StructureDescription);
#! [ "S3", "S3", "C2" ]
#! @EndExampleSession 

#! Alternatively, if $A$ is a subgroup of $\mathrm{Aut}(G)$, then
#! `Automizer(A, H)` returns the subgroup $\mathrm{Aut}_A(H)$ of $\mathrm{Aut}(H)$ given by:
#! 
#! $$\mathrm{Aut}_A(H) := \langle \alpha|_H \mid \alpha \in A, \alpha(H) = H \rangle.$$
#! 

#! @BeginExampleSession
#! gap> S := SmallGroup(5^6, 642);
#! <pc group of size 15625 with 6 generators>
#! gap> V := Group(S.2, S.6);
#! <pc group with 2 generators>
#! gap> AutS := AutomorphismGroup(S);
#! <group of size 1562500 with 10 generators>
#! gap> AutSV := Automizer(AutS, V);
#! <group with 7 generators>
#! gap> AutV := AutomorphismGroup(V);
#! <group with 4 generators>
#! gap> n := NiceMonomorphism(AutV);
#! <action isomorphism>
#! gap> AutV := n(AutV);
#! <permutation group with 4 generators>
#! gap> AutSV := n(AutSV);
#! <permutation group with 7 generators>
#! gap> Index(AutV, AutSV);
#! 24
#! gap> Size(AutSV);
#! 20
#! @EndExampleSession 
#! @EndGroup

#! @BeginGroup 
#! @GroupTitle Restriction of homomorphisms
#! @Description 
#!
#! Let $\phi \colon A \to B$ be a group homomorphism, and let $X \leq A$. The function 
#! `RestrictedHomomorphism(phi, X)` returns the surjective group homomorphism 
#! $\phi|_X \colon X \to \phi(X)$ given by restriction. If $\phi$ is also an isomorphism that fixes $X$, 
#! then the function `RestrictedAutomorphism(phi, X)` returns the group automorphism 
#! $\phi|_X \colon X \to \phi(X)$ given by restriction.
#! 
#! @Arguments phi X
DeclareOperation("RestrictedHomomorphism", [IsGroupHomomorphism, IsGroup]);
#! @Arguments phi X
#! @Returns a group automorphism
DeclareOperation("RestrictedAutomorphism", [IsGroupHomomorphism and IsBijective, IsGroup]);
#! @EndGroup


#! @BeginGroup 
#! @GroupTitle Transfer homomorphism 

#! @Description 
#!
#! Let $G$ be a finite group and $S \leq G$. The operation `TransferHomomorphism(G, S)` returns the transfer homomorphism
#! $\mathrm{tr}_S^G \colon G \to S/S'$. Moreover, if $S$ is a $p$-group, then the operation `TransferHomomorphismFp(G, S)` 
#! returns the transfer homomorphism $\mathrm{tr'}_S^G \colon G \to S/\Phi(S)$.
#! 
#! @Arguments G S
#! @Returns a homomorphism
DeclareOperation("TransferHomomorphism", [IsGroup, IsGroup]);
#! @Arguments G S
DeclareOperation("TransferHomomorphismFp", [IsGroup, IsPGroup]);
#! @EndGroup

#! @Section Semi-characteristic subgroups

#! Let $S$ be a $p$-group and $A \leq S$. We say that $S$ is __semi-characteristic__ in $S$ if 
#! * $A$ is normal in $S$, and
#! * $A$ is fixed by $O^p(O^{p'}(\mathrm{Aut}(S)))$.

#! @Description 
#!
#! Let $S$ be a $p$-group. The operation `SemiAutomorphismGroup` returns the
#! semi-automorphism group of $S$, which is given by $\langle \mathrm{Inn}(S), O^p(O^{p'}(\mathrm{Aut}(S)))\rangle$.
#! 
#! @Arguments S
#! @Returns a subgroup of Aut(S)
DeclareAttribute("SemiAutomorphismGroup", IsPGroup);

#! @Description 
#!
#! Let $S$ be a $p$-group. The operation `SemiCharacteristicSubgroups` returns all the semi-characteristic subgroups
#! of $S$. These are the normal subgroups of $S$ fixed by $O^p(O^{p'}(\mathrm{Aut}(S)))$.
#! 
#! @Arguments S
#! @Returns a list
DeclareAttribute("SemiCharacteristicSubgroups", IsPGroup);

#! @Description 
#!
#! Let $S$ be a $p$-group and $A$ be a subgroup of $S$. The operation `IsSemiCharacteristic` checks whether
#! $E$ is a semi-characteristic in $S$. That is, we check whether:
#! 
#! * $E$ is normal in $S$, and
#! * $E$ is fixed by $O^p(O^{p'}(\mathrm{Aut}(S)))$.
#! 
#! @Arguments S A
#! @Returns true or false
DeclareOperation("IsSemiCharacteristic", [IsPGroup, IsPGroup]);

#! @Description 
#!
#! Let $S$ be a $p$-group and $A$ be a subgroup of $S$. The operation `SemiCharacteristicClosure` returns the
#! smallest semi-characteristic subgroup of $S$ containing $A$. This is the intersection of all semi-characteristic
#! subgroups of $S$ containing $A$.
#! 
#! @Arguments S A
#! @Returns a subgroup of Aut(E)
DeclareOperation("SemiCharacteristicClosure", [IsPGroup, IsPGroup]);

#! @BeginExample
#! gap> S := SmallGroup(2^8, 6331);
#! <pc group of size 256 with 8 generators>
#! gap> E1 := Group(S.1, S.2, S.4, S.5, S.6, S.7, S.8);
#! <pc group with 7 generators>
#! gap> E2 := Group(S.1, S.2, S.4, S.5, S.7, S.8);
#! <pc group with 6 generators>
#! gap> A := Group(S.5*S.8);
#! <pc group with 1 generator>
#! gap> AutomorphismGroup(E1);
#! <group of size 6144 with 12 generators>
#! gap> AutomorphismGroup(E2);
#! <group of size 12288 with 13 generators>
#! gap> IsCharacteristicSubgroup(E1, A);
#! false
#! gap> IsCharacteristicSubgroup(E2, A);
#! false
#! gap> IsPGroup(E1);
#! true
#! gap> IsPGroup(E2);
#! true
#! gap> SemiAutomorphismGroup(E1);
#! <group of size 384 with 8 generators>
#! gap> SemiAutomorphismGroup(E2);
#! <group of size 3072 with 11 generators>
#! gap> IsPGroup(A);
#! true
#! gap> IsSemiCharacteristic(E1, A);
#! true
#! gap> IsSemiCharacteristic(E2, A);
#! false
#! gap> SemiCharacteristicClosure(E2, A);
#! Group([ f4, f5, f8, f4*f5, f4*f8, f5*f8, f4*f5*f8 ])
#! @EndExample 
