#
# The package's methods for groups of automorphisms extend \^ and
# CommutatorSubgroup to subgroups and automorphisms of an overgroup; the
# cases the GAP library already handles must be left to the library.
#
gap> START_TEST("automorphism-groups.tst");

# conjugation and commutators within a single automorphism group
gap> G := SymmetricGroup(4);;
gap> A := AutomorphismGroup(G);;
gap> t := InnerAutomorphism(G, (1,2));;
gap> A^A.1 = A;
true
gap> Size(CommutatorSubgroup(A, Group(t)));
12

# Aut_S(V) moved by an element and by an automorphism of S
gap> S := DihedralGroup(16);;
gap> V := First(AllSubgroups(S),
>              U -> Size(U) = 4 and IsElementaryAbelian(U) and not IsNormal(S, U));;
gap> g := First(S, x -> V^x <> V);;
gap> AutSV := Automizer(S, V);;
gap> Size(AutSV);
2
gap> AutomorphismDomain(AutSV^g) = V^g;
true
gap> Size(AutSV^g);
2
gap> phi := ConjugatorAutomorphism(S, g);;
gap> AutomorphismDomain(AutSV^phi) = Image(phi, V);
true
gap> Size(AutSV^phi);
2

# [Aut(S), S] for S dihedral of order 8
gap> S := DihedralGroup(8);;
gap> Size(CommutatorSubgroup(AutomorphismGroup(S), S));
4

#
gap> STOP_TEST("automorphism-groups.tst");
