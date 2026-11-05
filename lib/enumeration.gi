# Enumeration of all saturated fusion systems on a p-group.

# based on [PS_MAGMA, Lemma 4.5]. Depends on the classification of finite simple groups
InstallMethod(HasStronglyPEmbeddedSubgroup, "for a p-group and a subgroup",
    [IsGroup, IsPGroup], function(G, S)    
	local p, i, K, M, d, n, q;
    
    if IsTrivial(S) then
        return false; 
    fi;
    p := PrimePGroup(S);

    if not IsTrivial(PCore(G, p)) then
        return false;
    fi;

    i := SPESylowType(S);

	if i = 0 then
		return true;
    # G cannot be soluble in the p-rank >1 case.
	elif IsSolvableGroup(G) then
		return false;
    fi;

	# We are now in the p-rank >1 case.
    K := CoprimeResidual(G, [p]);
    M := K/SylowComplement(FittingSubgroup(K), p);
    
    #If G has Spe sbgp, then M lies on a list of almost simple groups.
    if not IsSimpleGroup(M) then		#Only 2 possibilities that are almost simple but not simple.
        # PSL_2(8):C_3
        if p = 3 and Size(M) = 1512 and IsAlmostSimpleGroup(M) then
            return ForAny( MaximalSubgroupClassReps(M), H -> IdGroup(H)=IdGroup(PSL(2,8)) );
        # Sz(32):C_5
        elif p = 5 and Size(M) = 162688000 then	
            return true;
        fi;
    else	
        d := IsomorphismTypeInfoFiniteSimpleGroup(M);

        if d.series = "Spor" then
            return (d.name = "M(11)" and p = 3) or (d.name in ["Fi(22)", "Mc"] and p = 5) or (d.name = "J4" and p = 11);
        # Classical gps of Lie type
        elif IsList(d.parameter) then		
            n:=d.parameter[1];
            q:=d.parameter[2];
            if SmallestRootInt(q) = p then
                return 
                    (n = 2 and d.series = "L" and q <> p) or # L_2(q)
                    (n = 3-1 and q <> 2 and d.series = "2A"); # U_3(q)
            else
                return (n = 3 and q = 4 and p = 3 and d.series = "L"); # L_3(4)
            fi;
        # Alternating groups and exceptional groups of Lie type
        else	
            q := d.parameter;
            if d.series = "A" and (
                q = 2*p or # Alt(2p)
                (q = 5 and p = 2) or # A_5 \cong L_2(4) 
                (q = 6 and p = 3)) then # A_6 \cong L_2(9)
                return true;
            # Sz(2^{2n+1})
            elif d.series = "2B" and p = 2 then
                return true;
            # 2G_2(3^{2n+1})
            elif d.series = "2G" and p = 3 then
                return true;
            # 2F_4(2)'
            elif d.series = "2F" and p = 3 and q = 2 then
                return true;
            fi;
        fi;
    fi;

    return false;
end);

# lists of automorphisms of S generating a complement C to Inn(S) in Aut_F(S), for the p'-subgroups C
# of Out(S) up to conjugacy. If P = O_p(Out(S)), these correspond to the p'-subgroups of Out(S)/P up to conjugacy,
# since two complements of P in a subgroup of Out(S) are conjugate (Schur-Zassenhaus).
BindGlobal("FS_AutFSChoices", function(S, nice, InnP, hom)
    local p, OutP, qhom, Q, reps, C, comp;
    p := PrimePGroup(S);
    OutP := Image(hom);
    qhom := NaturalHomomorphismByNormalSubgroup(OutP, PCore(OutP, p));
    Q := Image(qhom);
    if Size(Q) = 1 then
        return [[]];
    fi;
    reps := Filtered(List(ConjugacyClassesSubgroups(Q), Representative), C -> Size(C) mod p <> 0);
    return List(reps, function(C)
        if Size(C) = 1 then
            return [];
        fi;
        C := PreImage(hom, PreImage(qhom, C));
        # the Sylow p-subgroup of C is normal, so the complements are the Hall p'-subgroups
        if IsSolvableGroup(C) then
            comp := HallSubgroup(C, Difference(PrimeDivisors(Size(C)), [p]));
        else
            comp := ComplementClassesRepresentatives(C, SylowSubgroup(C, p))[1];
        fi;
        return List(GeneratorsOfGroup(comp), x -> PreImagesRepresentative(nice, x));
    end);
end);

InstallMethod(OvergroupsWithSylowSubgroup, "Parker-Semeraro, Appendix B", [IsGroup, IsGroup], function(G, T)
    local p, NGT, SubnormalClosure, Invariant, AddUpToConjugacy, queue, i, X, M, pair, H0, N, hom, K, H, res;
    if not IsPGroup(T) or Size(T) = 1 then
        Error("<T> must be a nontrivial p-group");
    fi;
    p := PrimePGroup(T);
    NGT := Normalizer(G, T);
    # smallest subnormal subgroup of X containing T
    SubnormalClosure := function(X)
        local Y;
        repeat
            Y := X;
            X := NormalClosure(X, T);
        until Size(X) = Size(Y);
        return X;
    end;
    # an invariant of Y under conjugation in G
    Invariant := function(Y)
        if IsPermGroup(G) then
            return [Size(Y), Collected(List(OrbitsDomain(Y, MovedPoints(G)), Length))];
        fi;
        return Size(Y);
    end;
    # list[2] contains the invariants of the groups in list[1]
    AddUpToConjugacy := function(list, Y)
        local inv;
        inv := Invariant(Y);
        if ForAll([1..Length(list[1])], i -> list[2][i] <> inv or RepresentativeAction(NGT, list[1][i], Y) = fail) then
            Add(list[1], Y);
            Add(list[2], inv);
        fi;
    end;
    # Candidates for O^{p'}(H): if O^{p'}(H) = H0 < X = sn(X, T), then H0 lies in a maximal subgroup of X which is conjugate
    # under N_X(T) to M^(g^-1), where M is a class representative of maximal subgroups and T^g <= M. Then H0 <= sn(M^(g^-1), T).
    queue := [[], []];
    AddUpToConjugacy(queue, SubnormalClosure(G));
    AddUpToConjugacy(queue, T);
    i := 0;
    while i < Length(queue[1]) do
        i := i + 1;
        X := queue[1][i];
        if Size(X) > Size(T) then
            for M in MaximalSubgroupClassReps(X) do
                if Size(M) mod Size(T) = 0 then
                    for pair in ContainedConjugates(X, M, T) do
                        AddUpToConjugacy(queue, SubnormalClosure(M^(pair[2]^-1)));
                    od;
                fi;
            od;
        fi;
    od;
    queue := queue[1];
    Info(InfoFusion, 2, Length(queue), " subnormal closures of T up to N_G(T)-conjugacy");
    # H = H0 N_H(T), where N_H(T) <= N_{N_G(T)}(H0) contains T as a Sylow p-subgroup
    res := [[], []];
    for H0 in Filtered(queue, X -> PadicValuation(Size(X), p) = PadicValuation(Size(T), p)) do
        N := Normalizer(NGT, H0);
        hom := NaturalHomomorphismByNormalSubgroup(N, T);
        for K in List(ConjugacyClassesSubgroups(Image(hom)), Representative) do
            if Size(K) mod p <> 0 then
                H := ClosureGroup(H0, PreImage(hom, K));
                if PadicValuation(Size(H), p) = PadicValuation(Size(T), p) then
                    AddUpToConjugacy(res, H);
                fi;
            fi;
        od;
    od;
    return res[1];
end);

# [SAM14, Theorem 6.9, Proposition 6.10]: if E is essential in a saturated fusion system and E/Phi(E) has rank r, then
# N = Out_S(E) is a Sylow p-subgroup of a group with a strongly p-embedded subgroup acting faithfully on E/Phi(E), so
# |N|^2 <= p^r and N is cyclic, quaternion, elementary abelian, or of one of the following types: for p = 2, a Suzuki
# 2-group with Omega(N) = Z(N) = Phi(N) = N' and |N| = |Z(N)|^2 or |Z(N)|^3 (Sz(2^n), PSU(3, 2^n)); for odd p, a group of
# exponent p with Z(N) = N' = Phi(N) elementary abelian of order |N|^(1/3) (PSU(3, p^n)); for p = 3, 5, the extraspecial
# group p^(1+2)_-; for p = 3, a group with |N| = |Z(N)|^3 = 3^(6n+3), n >= 1, and Omega(N) = Phi(N) = N' = Z_2(N)
# elementary abelian of order |Z(N)|^2 (Ree groups). The bound on |N| is [PS_MAGMA, Lemma 4.7, Proposition 4.8(4)] and
# the list of types is [PS_MAGMA, Corollary 4.6, Proposition 4.8(3)]. For p = 2, all of this follows from Bender's
# theorem; for odd p, it depends on the classification of finite simple groups.
BindGlobal("FS_IsStronglyEmbeddedSylowType", function(N, p, r)
    local Z, Om, Phi, Der;
    if Size(N)^2 > p^r then
        return false;
    fi;
    if IsCyclic(N) or IsElementaryAbelian(N) then
        return true;
    fi;
    Om := Omega(N, p);
    if Size(Om) = p then
        # a noncyclic p-group with a unique subgroup of order p is generalized quaternion
        return true;
    fi;
    Z := Center(N);
    Phi := FrattiniSubgroup(N);
    Der := DerivedSubgroup(N);
    if p = 2 then
        return Om = Z and Phi = Z and Der = Z and Size(N) in [Size(Z)^2, Size(Z)^3];
    fi;
    if Exponent(N) = p and IsElementaryAbelian(Z) and Der = Z and Phi = Z and Size(N) = Size(Z)^3 then
        return true;
    fi;
    if p in [3, 5] and Size(N) = p^3 and Exponent(N) = p^2 and not IsAbelian(N) then
        return true;
    fi;
    return p = 3 and Size(N) > 27 and Size(N) = Size(Z)^3 and PadicValuation(Size(N), 3) mod 6 = 3 and
           Om = Phi and Om = Der and Om = FS_SecondCentre(N) and IsElementaryAbelian(Om) and Size(Om) = Size(Z)^2;
end);

# Necessary conditions for an S-centric subgroup E < S to be essential in a saturated fusion system on S which only
# involve N_S(E). All of them hold for every saturated fusion system (not only reduced ones), cf. [PS_MAGMA,
# Proposition 4.8]:
# * E is not cyclic: otherwise Out(E) is abelian and Out_S(E) <= O_p(Out(E)), contradicting [PS_MAGMA, Proposition 4.8(2)].
# * [OV, Lemma 3.4]: if g in N_S(E) acts trivially on E/Theta Phi(E) and on Theta Phi(E)/Phi(E) for a characteristic
#   subgroup Theta of E, then the conjugation by g lies in O_p(Aut(E)) (Burnside), so g in E by [PS_MAGMA,
#   Proposition 4.8(2)]. As in [AOV17, Proposition 2.3(g)], we take Theta = 1, Z(E), Z_2(E).
# * FS_IsStronglyEmbeddedSylowType (uses the classification of finite simple groups for odd p).
# * For p = 2 the conditions of [AOV17, Proposition 2.3(a),(c)-(f)] for critical subgroups, which include all essential
#   subgroups by [OV, Proposition 3.2]. They follow from [OV, Lemma 3.6(a)] (the test Zed0Test) and from [OV, Lemma 1.7]
#   applied to Out_F(E) acting faithfully on V = E/Phi(E) as in the proof of [OV, Proposition 3.3], with
#   S0 = Out_S(E) of order 2^k and d = dim(V):
#   - [OV, Proposition 3.3(a)]: S0 is cyclic or Z(S0) consists of the elements of order at most 2; if Z(S0) is not
#     cyclic, then |S0| = |Z(S0)|^m with m <= 3;
#   - [OV, Lemma 1.7(a)] = [PS_MAGMA, Proposition 4.8(4)] for p = 2: d >= 2k;
#   - [OV, Lemma 1.7(b)]: if Z(S0) is elementary abelian of order 2^n, then dim([s, V]) >= n for all 1 <> s in S0;
#   - [OV, Proposition 3.3(c)]: if k >= 2, then dim([s, V]) >= 2 for all 1 <> s in S0;
#   - [OV, Lemma 1.7(c)]: if S0 is cyclic or quaternion of order 2^k >= 8, then d >= 3 2^(k-2) and
#     dim([s, V]) >= 2^(k-2) for all 1 <> s in S0.
#   These rest on Bender's classification of groups with a strongly embedded subgroup, the Brauer-Suzuki theorem and
#   Zsigmondy's theorem.
# Zed0Test is only proved for p = 2. The tests RankTest and ValidAutTest of IsProtoEssential are replaced by
# FS_IsStronglyEmbeddedSylowType and the exact computation of the candidates for Out_F(E) in FS_EssentialData.
BindGlobal("FS_IsPotentiallyEssential", function(S, E)
    local p, N, Phi, Theta, T, C, hom, S0, Z, k, d, dims, s, n;
    p := PrimePGroup(S);
    if IsCyclic(E) then
        return false;
    fi;
    N := Normalizer(S, E);
    Phi := FrattiniSubgroup(E);
    for Theta in [TrivialSubgroup(E), Center(E), FS_SecondCentre(E)] do
        T := ClosureGroup(Phi, Theta);
        C := CentralizerMod(N, E, T);
        if Size(T) > Size(Phi) then
            C := Intersection(C, CentralizerMod(N, T, Phi));
        fi;
        if Size(C) > Size(E) then
            Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails [OV, Lemma 3.4]");
            return false;
        fi;
    od;
    hom := NaturalHomomorphismByNormalSubgroup(N, E);
    S0 := Image(hom);
    d := Log(Size(E) / Size(Phi), p);
    if not FS_IsStronglyEmbeddedSylowType(S0, p, d) then
        Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails [SAM14, Theorem 6.9]");
        return false;
    fi;
    if p = 2 then
        if not Zed0Test(S, E) then
            Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails [OV, Lemma 3.6(a)]");
            return false;
        fi;
        Z := Center(S0);
        k := Log(Size(S0), 2);
        if not IsCyclic(S0) then
            if not IsElementaryAbelian(Z) or Size(Omega(S0, 2)) <> Size(Z) or
               (not IsCyclic(Z) and not Size(S0) in [Size(Z), Size(Z)^2, Size(Z)^3]) then
                Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails [OV, Proposition 3.3(a)]");
                return false;
            fi;
        fi;
        # dimensions of [s, E/Phi(E)] for representatives s of the nontrivial classes of S0
        dims := [];
        for s in List(ConjugacyClasses(S0), Representative) do
            if s <> One(S0) then
                s := PreImagesRepresentative(hom, s);
                Add(dims, Log(Size(ClosureGroup(Phi, List(GeneratorsOfGroup(E), x -> Comm(x, s)))) / Size(Phi), 2));
            fi;
        od;
        n := Log(Size(Z), 2);
        if d < 2 * k or (k >= 2 and Minimum(dims) < 2) or (IsElementaryAbelian(Z) and Minimum(dims) < n) or
           (k >= 3 and Size(Omega(S0, 2)) = 2 and (d < 3 * 2^(k - 2) or Minimum(dims) < 2^(k - 2))) then
            Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails [OV, Lemma 1.7]");
            return false;
        fi;
    fi;
    return true;
end);

# Data of a potentially essential subgroup E of S which only depend on the Aut(S)-orbit of E: Out(E), Out_S(E),
# N = N_{Out(E)}(Out_S(E)) and representatives Y0s up to N-conjugacy of the subgroups Y of Out(E) with Sylow p-subgroup
# Out_S(E), O_p(Y) = 1 and a strongly p-embedded subgroup, i.e. of the candidates for Out_F(E) for saturated fusion
# systems F on S in which E is essential, together with NY0s[i] = N_{Y0s[i]}(Out_S(E)). Returns fail if there are none. The tests used besides the definition hold for every saturated fusion system:
# * [PS_MAGMA, Proposition 4.8(2)]: Aut_S(E) meets O_p(Aut(E)) in Inn(E);
# * [PS_MAGMA, Lemma 4.4]: if Out_S(E) has an elementary abelian subgroup of order p^2 and Y has a strongly p-embedded
#   subgroup, then Y/O_{p'}(Y) is almost simple, so Y and Out(E) are not soluble ([PS_MAGMA, Proposition 4.8(5)]);
# * for p = 2, [OV, Proposition 3.3(b)]: N_{Out(E)}(Out_S(E)) is transitive on the involutions of Out_S(E).
BindGlobal("FS_EssentialData", function(S, E)
    local p, AutE, niceE, AE, InnE, AutSE, hom, OutE, OutSE, rank2, N, Y0s, Y0;
    p := PrimePGroup(S);
    AutE := AutomorphismGroup(E);
    niceE := NiceMonomorphism(AutE);
    AE := Image(niceE);
    InnE := Image(niceE, InnerAutomorphismsAutomorphismGroup(AutE));
    AutSE := Group(List(GeneratorsOfGroup(Normalizer(S, E)), n -> Image(niceE, ConjugatorAutomorphismNC(E, n))), One(AE));
    if Size(Intersection(AutSE, PCore(AE, p))) <> Size(InnE) then
        Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails [PS_MAGMA, Proposition 4.8(2)]");
        return fail;
    fi;
    hom := NaturalHomomorphismByNormalSubgroup(AE, InnE);
    OutE := Image(hom);
    OutSE := Image(hom, AutSE);
    # a p-group has an elementary abelian subgroup of order p^2 iff it has more than one subgroup of order p
    rank2 := Size(Omega(OutSE, p)) > p;
    if rank2 and IsSolvableGroup(OutE) then
        Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails [PS_MAGMA, Proposition 4.8(5)]");
        return fail;
    fi;
    N := Normalizer(OutE, OutSE);
    if p = 2 and Length(OrbitsDomain(N, Filtered(AsList(OutSE), x -> Order(x) = 2), OnPoints)) > 1 then
        Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails [OV, Proposition 3.3(b)]");
        return fail;
    fi;
    Y0s := Filtered(OvergroupsWithSylowSubgroup(OutE, OutSE), Y0 -> Size(PCore(Y0, p)) = 1 and
                    not (rank2 and IsSolvableGroup(Y0)) and HasStronglyPEmbeddedSubgroup(Y0, OutSE));
    if Y0s = [] then
        return fail;
    fi;
    return rec(E := E, niceE := niceE, hom := hom, OutE := OutE, OutSE := OutSE, N := N, Y0s := Y0s,
               NY0s := List(Y0s, Y0 -> Normalizer(Y0, OutSE)));
end);

# The candidates Y for Out_F(E) from the data ed of FS_EssentialData(S, E) which contain the subgroup OutB of Out(E)
# induced by Aut_F(S), as pairs [Y, b] where b states whether N_Y(Out_S(E)) = OutB. If forced is true, only those with
# b = true are returned: they are the conjugates of Y0^n by N_N(OutB), where Y0 runs through ed.Y0s with
# N_{Y0}(Out_S(E))^n = OutB for some n in N. Otherwise all N-conjugates of the elements of ed.Y0s are computed once
# and stored in ed. Since many choices of Aut_F(S) induce the same subgroup OutB, the results are stored in ed.cache.
BindGlobal("FS_OutAutomizerCandidates", function(ed, OutB, forced)
    local res, NB, i, n, Y, x;
    if not IsBound(ed.cache) then
        ed.cache := [];
    fi;
    for x in ed.cache do
        if x[1] = forced and Size(x[2]) = Size(OutB) and x[2] = OutB then
            return x[3];
        fi;
    od;
    res := [];
    if forced then
        NB := Normalizer(ed.N, OutB);
        for i in [1..Length(ed.Y0s)] do
            if Size(ed.NY0s[i]) = Size(OutB) then
                n := RepresentativeAction(ed.N, ed.NY0s[i], OutB);
                if n <> fail then
                    Append(res, List(Orbit(NB, ed.Y0s[i]^n, OnPoints), Y -> [Y, true]));
                fi;
            fi;
        od;
    else
        if not IsBound(ed.Ys) then
            ed.Ys := Concatenation(List(ed.Y0s, Y0 -> Orbit(ed.N, Y0, OnPoints)));
            ed.NYs := List(ed.Ys, Y -> Normalizer(Y, ed.OutSE));
        fi;
        for i in [1..Length(ed.Ys)] do
            if IsSubset(ed.Ys[i], OutB) then
                Add(res, [ed.Ys[i], Size(ed.NYs[i]) = Size(OutB)]);
            fi;
        od;
    fi;
    Add(ed.cache, [forced, OutB, res]);
    return res;
end);

# the subgroup of Out(E) induced by the list auts of automorphisms of S leaving E invariant, for the data ed of
# FS_EssentialData(S, E)
BindGlobal("FS_OutRestrictions", function(ed, auts)
    local E, gens;
    E := ed.E;
    gens := GeneratorsOfGroup(E);
    return Group(List(auts, a -> Image(ed.hom, Image(ed.niceE,
                     GroupHomomorphismByImagesNC(E, E, gens, List(gens, x -> Image(a, x)))))), One(ed.OutE));
end);

# Is the set key (of positive integers) the smallest element of its orbit under the group generated by the permutations gens?
BindGlobal("FS_IsMinimalInOrbit", function(gens, key)
    local orb, seen, k, g, img;
    orb := [key];
    seen := [key];
    k := 0;
    while k < Length(orb) do
        k := k + 1;
        for g in gens do
            img := OnSets(orb[k], g);
            if img < key then
                return false;
            fi;
            if not img in seen then
                AddSet(seen, img);
                Add(orb, img);
            fi;
        od;
    od;
    return true;
end);

# the group of automorphisms of beta(E) corresponding to the subgroup Y of Out(E), for the data ed of
# FS_EssentialData(S, E) and automorphisms beta, betainv = beta^-1 of S
BindGlobal("FS_TransportAutomizer", function(ed, Y, beta, betainv)
    local E, gens, X;
    E := Image(beta, ed.E);
    gens := GeneratorsOfGroup(E);
    X := List(GeneratorsOfGroup(PreImage(ed.hom, Y)), x -> PreImagesRepresentative(ed.niceE, x));
    X := Group(List(X, a -> GroupHomomorphismByImagesNC(E, E, gens,
                                List(gens, x -> Image(beta, Image(a, Image(betainv, x)))))), IdentityMapping(E));
    SetIsGroupOfAutomorphismsFiniteGroup(X, true);
    SetAutomorphismDomain(X, E);
    return X;
end);

InstallMethod(EssentialAutomizerCandidates, "for a p-group, a subgroup and a list of automorphisms",
    [IsPGroup, IsPGroup, IsList], function(S, E, AS)
    local p, ed, ASgrp, OutBE, isnormal, id;
    p := PrimePGroup(S);
    if E = S or not FS_IsSCentric(S, E) or not FS_IsPotentiallyEssential(S, E) then
        return [];
    fi;
    ed := FS_EssentialData(S, E);
    if ed = fail then
        return [];
    fi;
    # restrictions of the stabilizer of E in Aut_F(S)
    ASgrp := Group(Concatenation(AS, List(GeneratorsOfGroup(S), s -> ConjugatorAutomorphismNC(S, s))), IdentityMapping(S));
    OutBE := FS_OutRestrictions(ed, GeneratorsOfGroup(Stabilizer(ASgrp, E, function(Q, a) return Image(a, Q); end)));
    if PadicValuation(Size(OutBE), p) > PadicValuation(Size(ed.OutSE), p) then
        return [];
    fi;
    # if N_S(E) = S, every element of N_{Out_F(E)}(Out_S(E)) extends to S by receptivity
    isnormal := IsNormal(S, E);
    id := IdentityMapping(S);
    return List(FS_OutAutomizerCandidates(ed, OutBE, isnormal), Y -> FS_TransportAutomizer(ed, Y[1], id, id));
end);

# The largest subgroup of the intersection of S and the domains of the groups of automorphisms in auts which is invariant under
# Inn(S), the automorphisms in AS and the groups in auts. It is contained in O_p(F) for F = FusionSystemByAutomizers(S, AS, auts)
# by Alperin's fusion theorem (cf. [PS_MAGMA, Lemma 4.9]).
BindGlobal("FS_InvariantCore", function(S, AS, auts)
    local K, gens, changed, a, L;
    K := S;
    for a in auts do
        K := Intersection(K, AutomorphismDomain(a));
    od;
    gens := Concatenation(AS, List(GeneratorsOfGroup(S), s -> ConjugatorAutomorphismNC(S, s)),
                          Concatenation(List(auts, GeneratorsOfGroup)));
    repeat
        changed := false;
        for a in gens do
            L := Intersection(K, Image(a, K));
            if Size(L) < Size(K) then
                K := L;
                changed := true;
                if Size(K) = 1 then
                    return K;
                fi;
            fi;
        od;
    until not changed;
    return K;
end);

# rows of the matrix over GF(p) of the images in S/Phi(S) of the elements x^-1 a(x), where x runs through the
# generators of the domain of a and a through auts
BindGlobal("FS_FocalVectors", function(fhom, auts)
    local pcgs, res, a, x;
    pcgs := Pcgs(Image(fhom));
    res := [];
    for a in auts do
        for x in GeneratorsOfGroup(Source(a)) do
            Add(res, ExponentsOfPcElement(pcgs, Image(fhom, x^-1 * Image(a, x))) * One(GF(PrimePGroup(Source(fhom)))));
        od;
    od;
    return res;
end);

BindGlobal("FS_RankOfRows", function(rows)
    if rows = [] then
        return 0;
    fi;
    return RankMat(rows);
end);

InstallMethod(AllSaturatedFusionSystems, "for a p-group", [IsPGroup], function(S)
    local corefree, fullfocal, p, D, m, AutS, nice, AutP, InnP, hom, innS, gensP, mapsP, repkeys, Act, aorb, beta,
          j, i, a, id, queue, edata, orbits, results, AS, ASgens, ASP, mapsAS, asorb, T, found, cand, O, ed, sub, best,
          E, stab, betaP, b, binv, OutB, idx, c, fhom, dimV, ASvecs, sufvecs, chosen, Search, Process, tested, k, ASPgens, mapsASgens, kmax,
          trAS, ASedges, npairs, candOf, NASP, NASPgens, pairgens, t, tmap, img, l, o, Y, k2, posHom, PosMap;
    corefree := ValueOption("CoreFree") = true;
    fullfocal := ValueOption("FullFocal") = true;
    p := PrimePGroup(S);
    # [PS_MAGMA, Lemma 4.1]
    if corefree and IsAbelian(S) and Size(S) > 1 then
        return [];
    fi;
    D := FS_CentricData(S);
    m := Length(D.reps);
    AutS := AutomorphismGroup(S);
    nice := NiceMonomorphism(AutS);
    AutP := Image(nice);
    InnP := Image(nice, InnerAutomorphismsAutomorphismGroup(AutS));
    hom := NaturalHomomorphismByNormalSubgroup(AutP, InnP);
    innS := List(GeneratorsOfGroup(S), s -> ConjugatorAutomorphismNC(S, s));
    repkeys := List(D.reps, R -> FS_Key(D, R));
    # [j', t] for the image of reps[j] under the automorphism with position map pm
    Act := function(j, pm)
        return FS_IdentifyKey(D, Set(List(repkeys[j], i -> pm[i])));
    end;
    # Aut(S)-orbits on the S-classes of S-centric subgroups; beta[j] in AutP maps the first member of the orbit onto reps[j]
    gensP := SmallGeneratingSet(AutP);
    mapsP := List(gensP, g -> FS_PositionMap(D, PreImagesRepresentative(nice, g), [1..Size(S)]));
    # the action of Aut(S) on the positions of the elements of S, so that the position map of an element of AutP is
    # computed in a permutation group instead of evaluating an automorphism on all elements of S
    posHom := GroupHomomorphismByImagesNC(AutP, SymmetricGroup(Size(S)), gensP, List(mapsP, PermList));
    PosMap := x -> ListPerm(Image(posHom, x), Size(S));
    aorb := ListWithIdenticalEntries(m, 0);
    beta := [];
    orbits := [];
    for j in [1..m] do
        if aorb[j] = 0 then
            aorb[j] := j;
            beta[j] := One(AutP);
            queue := [j];
            k := 0;
            while k < Length(queue) do
                k := k + 1;
                i := queue[k];
                for a in [1..Length(gensP)] do
                    id := Act(i, mapsP[a]);
                    if aorb[id[1]] = 0 then
                        aorb[id[1]] := j;
                        beta[id[1]] := beta[i] * gensP[a] * Image(nice, ConjugatorAutomorphismNC(S, id[2]));
                        Add(queue, id[1]);
                    fi;
                od;
            od;
            Add(orbits, queue);
        fi;
    od;
    # potentially essential subgroups up to Aut(S)
    edata := [];
    for O in orbits do
        E := D.reps[O[1]];
        if E <> S and FS_IsPotentiallyEssential(S, E) then
            ed := FS_EssentialData(S, E);
            if ed <> fail then
                ed.orbit := O;
                Add(edata, ed);
            fi;
        fi;
    od;
    Info(InfoFusion, 1, Length(orbits), " Aut(S)-classes of S-centric subgroups, ", Length(edata),
         " of them potentially essential with ", List(edata, ed -> Length(ed.Y0s)), " classes of candidates for Out_F(E)");
    # [PS_MAGMA, Proposition 4.10(1)] applies to every candidate E with |N_S(E)| larger than all candidates
    kmax := Maximum(Concatenation([0], List(edata, ed -> Size(ed.E))));
    fhom := NaturalHomomorphismByNormalSubgroup(S, FrattiniSubgroup(S));
    dimV := Length(Pcgs(Image(fhom)));
    results := [];
    for AS in FS_AutFSChoices(S, nice, InnP, hom) do
        ASgens := Concatenation(AS, innS);
        ASPgens := List(ASgens, x -> Image(nice, x));
        ASP := Group(ASPgens, One(AutP));
        # [PS_MAGMA, Lemma 4.2], [DGMP, Corollary 6.2]: if p >= 5 and Aut_F(S) is a p-group, then foc(F) < S
        if fullfocal and p >= 5 and Size(ASP) = Size(InnP) then
            continue;
        fi;
        mapsASgens := List(ASPgens, PosMap);
        mapsAS := mapsASgens{[1..Length(AS)]};
        ASedges := FS_AutomizerEdgesByMaps(D, S, mapsAS);
        # Aut_F(S)-orbits on the S-classes of S-centric subgroups; trAS[j] in ASP maps reps[asorb[j]] onto reps[j]
        asorb := ListWithIdenticalEntries(m, 0);
        trAS := [];
        for j in [1..m] do
            if asorb[j] = 0 then
                asorb[j] := j;
                trAS[j] := One(AutP);
                queue := [j];
                k := 0;
                while k < Length(queue) do
                    k := k + 1;
                    i := queue[k];
                    for a in [1..Length(mapsAS)] do
                        id := Act(i, mapsAS[a]);
                        if asorb[id[1]] = 0 then
                            asorb[id[1]] := j;
                            trAS[id[1]] := trAS[i] * ASPgens[a] * Image(nice, ConjugatorAutomorphismNC(S, id[2]));
                            Add(queue, id[1]);
                        fi;
                    od;
                od;
            fi;
        od;
        # candidates: for each Aut_F(S)-orbit of potentially essential subgroups the representative E with |N_S(E)|
        # maximal, the candidates for Aut_F(E) containing the restrictions of Aut_F(S), and whether they satisfy
        # N_{Aut_F(E)}(Aut_S(E)) = N_{Aut_F(S)}(E)|_E
        cand := [];
        for ed in edata do
            for k in Set(List(ed.orbit, j -> asorb[j])) do
                sub := Filtered(ed.orbit, j -> asorb[j] = k);
                best := sub[PositionMaximum(List(sub, j -> Size(D.norm[j])))];
                E := D.reps[best];
                stab := FS_StabilizerOfKey(ASPgens, mapsASgens, repkeys[best], One(AutP));
                betaP := beta[best];
                OutB := FS_OutRestrictions(ed, List(GeneratorsOfGroup(stab^(betaP^-1)), x -> PreImagesRepresentative(nice, x)));
                if PadicValuation(Size(OutB), p) > PadicValuation(Size(ed.OutSE), p) then
                    continue;
                fi;
                idx := FS_OutAutomizerCandidates(ed, OutB, Size(D.norm[best]) > kmax);
                if idx = [] then
                    continue;
                fi;
                b := PreImagesRepresentative(nice, betaP);
                binv := PreImagesRepresentative(nice, betaP^-1);
                c := rec(ed := ed, b := b, binv := binv, betaP := betaP, j := best, size := Size(E),
                         nsize := Size(D.norm[best]), Ys := List(idx, x -> x[1]), ext := List(idx, x -> x[2]));
                if c.nsize < Size(S) then
                    c.jN := FS_IdentifyCentricSubgroup(S, D, D.norm[best])[1];
                fi;
                Add(cand, c);
            od;
        od;
        for c in cand do
            c.auts := List(c.Ys, Y -> FS_TransportAutomizer(c.ed, Y, c.b, c.binv));
            c.edges := [];
            if fullfocal then
                c.vecs := List(c.auts, X -> FS_FocalVectors(fhom, GeneratorsOfGroup(X)));
            fi;
        od;
        cand := Filtered(cand, c -> c.auts <> []);
        SortBy(cand, c -> -c.size);
        Info(InfoFusion, 1, "Aut_F(S)/Inn(S) of order ", Size(ASP) / Size(InnP), ": ",
             List(cand, c -> Length(c.auts)), " automizer candidates");
        # [PS_MAGMA, Lemma 4.9] for all candidates: then O_p(F) <> 1 for all F with this Aut_F(S)
        if corefree and Size(FS_InvariantCore(S, AS, Concatenation(List(cand, c -> c.auts)))) > 1 then
            continue;
        fi;
        # foc(F) = S iff the vectors span S/Phi(S) ([AKO, Corollary I.7.5] and Burnside's basis theorem); sufvecs[i]
        # spans the contributions of all candidates from the i-th on
        if fullfocal then
            ASvecs := FS_FocalVectors(fhom, AS);
            sufvecs := [];
            sufvecs[Length(cand) + 1] := [];
            for i in Reversed([1..Length(cand)]) do
                sufvecs[i] := Concatenation(sufvecs[i + 1], Concatenation(cand[i].vecs));
                if sufvecs[i] <> [] then
                    sufvecs[i] := BaseMat(sufvecs[i]);
                fi;
            od;
            if FS_RankOfRows(Concatenation(ASvecs, sufvecs[1])) < dimV then
                continue;
            fi;
        else
            ASvecs := [];
        fi;
        # NASP = N_{Aut(S)}(Aut_F(S)) permutes the pairs (candidate i, automizer k), numbered by cand[i].pos[k]: if
        # beta in NASP maps E = cand[i].E onto an S-centric subgroup in the Aut_F(S)-orbit of cand[l].E, there is
        # gamma in Aut_F(S) with gamma(beta(E)) = cand[l].E, and cand[i].auts[k] is mapped to the conjugate of
        # cand[i].Ys[k] by the restriction of b_i beta gamma b_l^-1 to ed.E, where b_i = cand[i].betaP. This does not
        # depend on gamma since N_{Aut_F(S)}(cand[l].E) induces a subgroup of each candidate. All tests are invariant
        # under NASP, so only fusion data whose set of pairs is minimal in its orbit are tested.
        npairs := 0;
        candOf := [];
        for i in [1..Length(cand)] do
            cand[i].pos := [npairs + 1..npairs + Length(cand[i].auts)];
            npairs := npairs + Length(cand[i].auts);
            candOf[asorb[cand[i].j]] := i;
        od;
        NASP := fail;
        NASPgens := [];
        if npairs > 0 then
            NASP := Normalizer(AutP, ASP);
            NASPgens := SmallGeneratingSet(NASP);
        fi;
        pairgens := [];
        for t in NASPgens do
            if t in ASP then
                continue;
            fi;
            tmap := PosMap(t);
            img := [];
            for i in [1..Length(cand)] do
                c := cand[i];
                id := Act(c.j, tmap);
                if not IsBound(candOf[asorb[id[1]]]) then
                    break;
                fi;
                l := candOf[asorb[id[1]]];
                a := c.betaP * t * Image(nice, ConjugatorAutomorphismNC(S, id[2])) * trAS[id[1]]^-1 * trAS[cand[l].j] *
                     cand[l].betaP^-1;
                o := GeneratorsOfGroup(FS_OutRestrictions(c.ed, [PreImagesRepresentative(nice, a)]))[1];
                for k in [1..Length(c.Ys)] do
                    Y := c.Ys[k]^o;
                    k2 := PositionProperty(cand[l].Ys, Z -> Size(Z) = Size(Y) and Z = Y);
                    if k2 = fail then
                        break;
                    fi;
                    img[c.pos[k]] := cand[l].pos[k2];
                od;
                if k2 = fail then
                    break;
                fi;
            od;
            if Length(img) = npairs and IsDenseList(img) and IsPerm(PermList(img)) then
                Add(pairgens, PermList(img));
            else
                Info(InfoFusion, 2, "an element of N_Aut(S)(Aut_F(S)) does not permute the candidates");
                pairgens := fail;
                break;
            fi;
        od;
        if pairgens = fail then
            pairgens := [];
        fi;
        pairgens := Filtered(pairgens, g -> g <> ());
        # N_{Aut(S)}(Aut_F(S)) modulo Aut_F(S), for the isomorphism test
        T := fail;
        found := [];
        tested := 0;
        Process := function(chosen)
            local auts, F, new, same;
            if pairgens <> [] and not FS_IsMinimalInOrbit(pairgens, List(chosen, x -> cand[x[1]].pos[x[2]])) then
                return;
            fi;
            auts := List(chosen, x -> cand[x[1]].auts[x[2]]);
            if corefree and Size(FS_InvariantCore(S, AS, auts)) > 1 then
                return;
            fi;
            tested := tested + 1;
            F := FS_FusionSystemByAutomizersNC(S, AS, List(auts, X -> [AutomorphismDomain(X), GeneratorsOfGroup(X)]));
            F!.edgeParts := Concatenation([ASedges], List(chosen, function(x)
                local c;
                c := cand[x[1]];
                if not IsBound(c.edges[x[2]]) then
                    c.edges[x[2]] := FS_AutomizerEdges(D, AutomorphismDomain(c.auts[x[2]]),
                                                       GeneratorsOfGroup(c.auts[x[2]]));
                fi;
                return c.edges[x[2]];
            end));
            if IsSaturatedFusionSystem(F) and (not corefree or Size(PCoreOfFusionSystem(F)) = 1) then
                # invariants for the isomorphism test; k(F, 0) is only computed if the cheaper one agrees
                new := SortedList(List(CentricSubgroupClassRepresentatives(F), Q -> [Size(Q), Size(FS_AutomizerPerm(F, Q))]));
                same := Filtered(found, x -> x[1] = new and
                                 NumberOfCharactersOfFusionSystem(x[2]) = NumberOfCharactersOfFusionSystem(F));
                if same <> [] and T = fail then
                    if NASP = fail then
                        NASP := Normalizer(AutP, ASP);
                    fi;
                    T := List(RightTransversal(NASP, ASP), t -> PreImagesRepresentative(nice, t));
                fi;
                if ForAll(same, x -> ForAll(T, t -> not FS_IsImageFusionSystem(x[2], F, t))) then
                    Add(found, [new, F]);
                fi;
            fi;
        end;
        # depth first search through the subsets of cand with a choice of automizers, ordered by decreasing size
        Search := function(i, chosen, vecs)
            local c, n, required, k, v;
            if fullfocal and FS_RankOfRows(Concatenation(vecs, sufvecs[i])) < dimV then
                return;
            fi;
            if i > Length(cand) then
                Process(chosen);
                return;
            fi;
            Search(i + 1, chosen, vecs);
            c := cand[i];
            if chosen = [] then
                n := c.size;
            else
                n := cand[chosen[1][1]].size;
            fi;
            # [PS_MAGMA, Proposition 4.10(1)]: here n is the largest order of a chosen subgroup, and all chosen
            # subgroups of order n are known
            required := c.nsize > n or (c.nsize = n and
                        ForAll(chosen, x -> cand[x[1]].size < n or asorb[cand[x[1]].j] <> asorb[c.jN]));
            for k in [1..Length(c.auts)] do
                if c.ext[k] or not required then
                    v := vecs;
                    if fullfocal then
                        v := Concatenation(v, c.vecs[k]);
                        if v <> [] then
                            v := BaseMat(v);
                        fi;
                    fi;
                    Search(i + 1, Concatenation(chosen, [[i, k]]), v);
                fi;
            od;
        end;
        Search(1, [], ASvecs);
        Info(InfoFusion, 1, tested, " saturation tests, ", Length(found), " fusion systems");
        Append(results, List(found, x -> x[2]));
    od;
    return results;
end);
