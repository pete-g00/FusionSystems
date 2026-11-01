# Fusion systems given by fusion data, fusion graph, automizers and saturation.
# Internally, a group of automorphisms of a subgroup X of S is stored as a permutation group on
# the positions of AsSSortedList(X).

BindGlobal("FusionSystemFamily", NewFamily("FusionSystemFamily", IsFusionSystem));
DeclareRepresentation("IsFusionSystemRep", IsComponentObjectRep and IsAttributeStoringRep, []);
BindGlobal("FS_FusionSystemType", NewType(FusionSystemFamily, IsFusionSystem and IsFusionSystemRep));

# number of p-blocks of defect zero of X (all simple modules if X is a p'-group)
BindGlobal("FS_NumberOfDefectZeroBlocks", function(X, p)
    local pp;
    if Size(X) mod p <> 0 then
        return NrConjugacyClasses(X);
    fi;
    pp := p^PadicValuation(Size(X), p);
    return Sum(Filtered(CharacterDegrees(X), x -> x[1] mod pp = 0), x -> x[2]);
end);

BindGlobal("FS_IsSCentric", function(S, Q)
    return IsSubset(Q, Centralizer(S, Q));
end);

# conjugation by the elements in gens as permutations on the sorted element list elts
BindGlobal("FS_ConjugationPerms", function(elts, gens)
    return List(gens, g -> PermList(List(elts, x -> PositionSorted(elts, x^g))));
end);

# Subgroups of S are described by their keys: the (increasing) lists of positions of their elements in AsSSortedList(S).
BindGlobal("FS_Key", function(D, Q)
    return List(AsSSortedList(Q), x -> PositionSorted(D.eltsS, x));
end);

# data of S: S-conjugacy class representatives reps of S-centric subgroups, their normalizers and element lists, and the
# sorted list keys of the keys of all S-centric subgroups, where keyid[k] = [j, t] with Q^t = reps[j] for the subgroup Q
# with key keys[k]
BindGlobal("FS_CentricData", function(S)
    local hom, reps, D, j, t;
    if IsBound(S!.FS_CentricData) then
        return S!.FS_CentricData;
    fi;
    # S-centric subgroups contain Z(S)
    hom := NaturalHomomorphismByNormalSubgroup(S, Center(S));
    reps := List(ConjugacyClassesSubgroups(Image(hom)), C -> PreImage(hom, Representative(C)));
    reps := Filtered(reps, R -> FS_IsSCentric(S, R));
    D := rec(reps := reps,
             norm := List(reps, R -> Normalizer(S, R)),
             elts := List(reps, AsSSortedList),
             eltsS := AsSSortedList(S),
             keys := [],
             keyid := []);
    for j in [1..Length(reps)] do
        for t in RightTransversal(S, D.norm[j]) do
            Add(D.keys, Set(List(D.elts[j], x -> PositionSorted(D.eltsS, x^t))));
            Add(D.keyid, [j, t^-1]);
        od;
    od;
    SortParallel(D.keys, D.keyid);
    if IsComponentObjectRep(S) then
        S!.FS_CentricData := D;
    fi;
    return D;
end);

# [j, t] with Q^t = D.reps[j] for the subgroup Q with the given key, or fail if Q is not S-centric
BindGlobal("FS_IdentifyKey", function(D, key)
    local k;
    k := PositionSorted(D.keys, key);
    if k <= Length(D.keys) and D.keys[k] = key then
        return D.keyid[k];
    fi;
    return fail;
end);

# [j, t] with Q^t = D.reps[j] for the data D of FS_CentricData(S), or fail if Q is not S-centric
BindGlobal("FS_IdentifyCentricSubgroup", function(S, D, Q)
    return FS_IdentifyKey(D, FS_Key(D, Q));
end);

BindGlobal("FS_IdentifySubgroup", function(F, Q)
    return FS_IdentifyCentricSubgroup(F!.S, F!.data, Q);
end);

# list m with m[i] the position of the image of D.eltsS[i] under the map a, for the positions i in key
BindGlobal("FS_PositionMap", function(D, a, key)
    local m, i;
    m := [];
    for i in key do
        m[i] := PositionSorted(D.eltsS, Image(a, D.eltsS[i]));
    od;
    return m;
end);

InstallMethod(FusionSystemByAutomizers, "for a p-group, a list of automorphisms and a list of automizers",
    [IsPGroup, IsList, IsList], function(S, AS, L)
    local D, ess, X;
    D := FS_CentricData(S);
    ess := [];
    for X in L do
        if IsGroup(X) then
            Add(ess, [AutomorphismDomain(X), GeneratorsOfGroup(X)]);
        else
            Add(ess, X);
        fi;
    od;
    if ForAny(ess, e -> not FS_IsSCentric(S, e[1])) then
        Error("the subgroups in the fusion datum must be S-centric");
    fi;
    return Objectify(FS_FusionSystemType, rec(S := S, p := PrimePGroup(S), AS := AS, ess := ess, data := D,
        reps := D.reps, norm := D.norm, elts := D.elts));
end);

InstallMethod(UnderlyingPGroup, "for a fusion system", [IsFusionSystem], F -> F!.S);

InstallMethod(ViewString, "for a fusion system", [IsFusionSystem], function(F)
    return Concatenation("<fusion system on a group of order ", String(Size(F!.S)), " given by ",
                         String(Length(F!.ess)), " automizer(s) of proper subgroups>");
end);

InstallMethod(ViewObj, "for a fusion system", [IsFusionSystem], function(F)
    Print(ViewString(F));
end);

InstallMethod(PrintObj, "for a fusion system", [IsFusionSystem], function(F)
    Print(ViewString(F));
end);

# edges [i, j, m] of the fusion graph, where m[k] is the index in elts[j] of the image of elts[i][k]; bad contains the
# vertices from which a generator leads to a subgroup which is not S-centric
BindGlobal("FS_FusionGraphEdges", function(F)
    local S, D, edges, bad, j, x, data, E, keyE, sub, g, gm, k, img, id, i, s, t;
    S := F!.S;
    D := F!.data;
    edges := [];
    bad := [];
    for j in [1..Length(D.reps)] do
        for x in GeneratorsOfGroup(D.norm[j]) do
            Add(edges, [j, j, List(D.elts[j], y -> PositionSorted(D.elts[j], y^x))]);
        od;
    od;
    data := Concatenation([[S, F!.AS]], F!.ess);
    for E in data do
        # S-centric subgroups of E (positions in D.keys); for E = S the representatives suffice since Inn(S) is
        # contained in the fusion system
        if E[1] = S then
            keyE := [1..Size(S)];
            sub := List(D.reps, R -> PositionSorted(D.keys, FS_Key(D, R)));
        else
            keyE := FS_Key(D, E[1]);
            sub := Filtered([1..Length(D.keys)], k -> Length(D.keys[k]) <= Length(keyE) and IsSubsetSet(keyE, D.keys[k]));
        fi;
        for g in E[2] do
            gm := FS_PositionMap(D, g, keyE);
            for k in sub do
                img := Set(List(D.keys[k], i -> gm[i]));
                id := FS_IdentifyKey(D, img);
                i := D.keyid[k][1];
                if id = fail then
                    AddSet(bad, i);
                else
                    # the subgroup with key keys[k] is reps[i]^s
                    s := D.keyid[k][2]^-1;
                    t := id[2];
                    Add(edges, [i, id[1], List(D.elts[i], y -> PositionSorted(D.elts[id[1]],
                        D.eltsS[gm[PositionSorted(D.eltsS, y^s)]]^t))]);
                fi;
            od;
        od;
    od;
    return rec(edges := edges, bad := bad);
end);

# fusion graph: components, transport maps and automizers of the F-centric representatives
BindGlobal("FS_FusionGraph", function(F)
    local n, ge, adj, e, comp, root, tr, inv, good, aut, r, queue, members, u, w, A, pe, v, m, k;
    if IsBound(F!.good) then
        return F;
    fi;
    n := Length(F!.reps);
    ge := FS_FusionGraphEdges(F);
    adj := List([1..n], i -> []);
    for e in ge.edges do
        Add(adj[e[1]], e);
        if e[1] <> e[2] then
            Add(adj[e[2]], e);
        fi;
    od;
    comp := ListWithIdenticalEntries(n, 0);
    root := ListWithIdenticalEntries(n, 0);
    # tr[v][k] is the index in elts[v] of the image of the k-th element of the root of the component of v,
    # and inv[v] is the inverse list
    tr := [];
    inv := [];
    good := ListWithIdenticalEntries(n, false);
    aut := [];
    for r in [1..n] do
        if comp[r] = 0 then
            comp[r] := r;
            root[r] := r;
            tr[r] := [1..Length(F!.elts[r])];
            inv[r] := tr[r];
            queue := [r];
            members := [r];
            while queue <> [] do
                u := Remove(queue, 1);
                for e in adj[u] do
                    for w in [e[1], e[2]] do
                        if comp[w] = 0 then
                            comp[w] := r;
                            root[w] := r;
                            if w = e[2] then
                                tr[w] := e[3]{tr[u]};
                            else
                                m := [];
                                for k in [1..Length(e[3])] do
                                    m[e[3][k]] := k;
                                od;
                                tr[w] := m{tr[u]};
                            fi;
                            inv[w] := [];
                            for k in [1..Length(tr[w])] do
                                inv[w][tr[w][k]] := k;
                            od;
                            Add(queue, w);
                            Add(members, w);
                        fi;
                    od;
                od;
            od;
            if ForAll(members, v -> not v in ge.bad) then
                # Schreier generators of the vertex group at the root
                A := Group(FS_ConjugationPerms(F!.elts[r], GeneratorsOfGroup(F!.reps[r])), ());
                for e in ge.edges do
                    if comp[e[1]] = r then
                        pe := PermList(inv[e[2]]{e[3]{tr[e[1]]}});
                        if not pe in A then
                            A := ClosureGroup(A, pe);
                        fi;
                    fi;
                od;
                for v in members do
                    good[v] := true;
                    aut[v] := A^PermList(tr[v]);
                od;
            fi;
        fi;
    od;
    F!.root := root;
    F!.good := good;
    F!.aut := aut;
    return F;
end);

# Aut_F(Q) as permutation group on AsSSortedList(Q), or fail if Q is not F-centric
BindGlobal("FS_AutomizerPerm", function(F, Q)
    local id, j, t, eltsQ, perm;
    FS_FusionGraph(F);
    id := FS_IdentifySubgroup(F, Q);
    if id = fail or not F!.good[id[1]] then
        return fail;
    fi;
    j := id[1];
    t := id[2];
    eltsQ := AsSSortedList(Q);
    perm := PermList(List(eltsQ, x -> PositionSorted(F!.elts[j], x^t)));
    return F!.aut[j]^(perm^-1);
end);

InstallMethod(IsCentricInFusionSystem, "for a fusion system and a subgroup", [IsFusionSystem, IsGroup],
    function(F, Q)
    return FS_AutomizerPerm(F, Q) <> fail;
end);

InstallMethod(AutomizerInFusionSystem, "for a fusion system and a subgroup", [IsFusionSystem, IsGroup],
    function(F, Q)
    local A, elts, gens, pos;
    A := FS_AutomizerPerm(F, Q);
    if A = fail then
        Error("the subgroup is not centric in the fusion system");
    fi;
    elts := AsSSortedList(Q);
    gens := GeneratorsOfGroup(Q);
    pos := List(gens, x -> PositionSorted(elts, x));
    A := Group(List(GeneratorsOfGroup(A), a -> GroupHomomorphismByImagesNC(Q, Q, gens, List(pos, i -> elts[i^a]))),
               IdentityMapping(Q));
    SetIsGroupOfAutomorphismsFiniteGroup(A, true);
    SetAutomorphismDomain(A, Q);
    return A;
end);

InstallMethod(CentricSubgroupClassRepresentatives, "for a fusion system", [IsFusionSystem], function(F)
    FS_FusionGraph(F);
    return List(Filtered(Set(F!.root), r -> F!.good[r]), r -> F!.reps[r]);
end);

# surjectivity property for an F-centric subgroup P
BindGlobal("FS_SurjectivityProperty", function(F, P)
    local S, NSP, eltsP, AP, hom, Rbar, R, eltsR, AR, posP, St, res, AutRP, N;
    S := F!.S;
    NSP := Normalizer(S, P);
    if NSP = P then
        return true;
    fi;
    eltsP := AsSSortedList(P);
    AP := FS_AutomizerPerm(F, P);
    hom := NaturalHomomorphismByNormalSubgroup(NSP, P);
    for Rbar in List(ConjugacyClassesSubgroups(Image(hom)), Representative) do
        if Size(Rbar) > 1 then
            R := PreImage(hom, Rbar);
            eltsR := AsSSortedList(R);
            AR := FS_AutomizerPerm(F, R);
            if AR = fail then
                Error("FS_SurjectivityProperty: overgroup of a centric subgroup is not centric");
            fi;
            posP := List(eltsP, x -> PositionSorted(eltsR, x));
            St := Stabilizer(AR, Set(posP), OnSets);
            res := Group(List(GeneratorsOfGroup(St), g -> PermList(List(posP, i -> Position(posP, i^g)))), ());
            AutRP := Group(FS_ConjugationPerms(eltsP, GeneratorsOfGroup(R)), ());
            N := Normalizer(AP, AutRP);
            if not IsSubset(N, res) then
                Error("FS_SurjectivityProperty: inconsistent automizers");
            fi;
            if Size(res) <> Size(N) then
                Info(InfoFusion, 2, "surjectivity property fails for a subgroup of order ", Size(P));
                return false;
            fi;
        fi;
    od;
    return true;
end);

InstallMethod(IsSaturatedFusionSystem, "for a fusion system", [IsFusionSystem], function(F)
    local S, p, e, id, r, members, best, P;
    S := F!.S;
    p := F!.p;
    FS_FusionGraph(F);
    # generation by automorphisms of F-centric subgroups
    for e in F!.ess do
        id := FS_IdentifySubgroup(F, e[1]);
        if id = fail or not F!.good[id[1]] then
            Info(InfoFusion, 2, "a subgroup of the datum is not F-centric");
            return false;
        fi;
    od;
    # S is fully automized
    id := FS_IdentifySubgroup(F, S);
    if PadicValuation(Size(F!.aut[id[1]]), p) <> PadicValuation(Size(S) / Size(Center(S)), p) then
        Info(InfoFusion, 2, "S is not fully automized");
        return false;
    fi;
    # each class of F-centric subgroups contains a fully normalized subgroup with the surjectivity property;
    # if F is saturated, every fully normalized subgroup has this property
    for r in Set(F!.root) do
        if F!.good[r] then
            members := Filtered([1..Length(F!.reps)], v -> F!.root[v] = r);
            best := members[PositionMaximum(List(members, v -> Size(F!.norm[v])))];
            P := F!.reps[best];
            if PadicValuation(Size(F!.aut[best]), p) <> PadicValuation(Size(F!.norm[best]) / Size(Center(P)), p) then
                Info(InfoFusion, 2, "a fully normalized centric subgroup is not fully automized");
                return false;
            fi;
            if not FS_SurjectivityProperty(F, P) then
                return false;
            fi;
        fi;
    od;
    return true;
end);

InstallMethod(FocalSubgroupOfFusionSystem, "for a fusion system", [IsFusionSystem], function(F)
    local foc, v, elts, g;
    FS_FusionGraph(F);
    foc := TrivialSubgroup(F!.S);
    for v in [1..Length(F!.reps)] do
        if F!.good[v] then
            elts := F!.elts[v];
            for g in GeneratorsOfGroup(F!.aut[v]) do
                foc := ClosureGroup(foc, List([1..Length(elts)], k -> elts[k]^-1 * elts[k^g]));
            od;
        fi;
    od;
    return foc;
end);

InstallMethod(PCoreOfFusionSystem, "for a fusion system", [IsFusionSystem], function(F)
    local S, p, cr, v, P, Op, Q, nm;
    S := F!.S;
    p := F!.p;
    FS_FusionGraph(F);
    cr := Filtered([1..Length(F!.reps)], v -> F!.good[v] and
                   Size(PCore(F!.aut[v], p)) = Size(F!.reps[v]) / Size(Center(F!.reps[v])));
    Op := TrivialSubgroup(S);
    for Q in NormalSubgroups(S) do
        if Size(Q) > Size(Op) and ForAll(cr, v -> IsSubset(F!.reps[v], Q)) and
           ForAll(cr, function(v)
               nm := Set(List(AsSSortedList(Q), x -> PositionSorted(F!.elts[v], x)));
               return ForAll(GeneratorsOfGroup(F!.aut[v]), g -> OnSets(nm, g) = nm);
           end) then
            Op := Q;
        fi;
    od;
    return Op;
end);

# beta F1 beta^-1 = F2 for an automorphism beta of S?
BindGlobal("FS_IsImageFusionSystem", function(F1, F2, beta)
    local j, Q, A1, eltsQ, pi;
    FS_FusionGraph(F2);
    for j in [1..Length(F2!.reps)] do
        Q := PreImage(beta, F2!.reps[j]);
        A1 := FS_AutomizerPerm(F1, Q);
        if (A1 = fail) = F2!.good[j] then
            return false;
        fi;
        if A1 <> fail then
            eltsQ := AsSSortedList(Q);
            pi := PermList(List(eltsQ, x -> PositionSorted(F2!.elts[j], Image(beta, x))));
            if A1^pi <> F2!.aut[j] then
                return false;
            fi;
        fi;
    od;
    return true;
end);

# Aut_F(S) as a subgroup of the nice object of Aut(S)
BindGlobal("FS_AutomizerOfS", function(F, nice)
    local S, A;
    S := F!.S;
    A := AutomizerInFusionSystem(F, S);
    return Group(List(GeneratorsOfGroup(A), a -> Image(nice, a)), One(Range(nice)));
end);

InstallMethod(IsomorphismFusionSystems, "for two saturated fusion systems", [IsFusionSystem, IsFusionSystem],
    function(F1, F2)
    local S, AutS, nice, A1, A2, beta0, N, t, beta;
    S := F1!.S;
    if F2!.S <> S then
        Error("the fusion systems must be defined on the same group");
    fi;
    AutS := AutomorphismGroup(S);
    nice := NiceMonomorphism(AutS);
    A1 := FS_AutomizerOfS(F1, nice);
    A2 := FS_AutomizerOfS(F2, nice);
    beta0 := RepresentativeAction(Image(nice), A1, A2);
    if beta0 = fail then
        return fail;
    fi;
    N := Normalizer(Image(nice), A2);
    for t in RightTransversal(N, A2) do
        beta := PreImagesRepresentative(nice, beta0 * t);
        if FS_IsImageFusionSystem(F1, F2, beta) then
            return beta;
        fi;
    od;
    return fail;
end);

InstallMethod(NumberOfWeightsOfFusionSystem, "for a saturated fusion system", [IsFusionSystem], function(F)
    local r, P, Inn;
    FS_FusionGraph(F);
    return Sum(Filtered(Set(F!.root), r -> F!.good[r]), function(r)
        P := F!.reps[r];
        Inn := Group(FS_ConjugationPerms(F!.elts[r], GeneratorsOfGroup(P)), ());
        return FS_NumberOfDefectZeroBlocks(F!.aut[r] / Inn, F!.p);
    end);
end);

InstallMethod(NumberOfCharactersOfFusionSystem, "for a saturated fusion system", [IsFusionSystem], function(F)
    local k, r, P, elts, A, Inn, Z, o;
    FS_FusionGraph(F);
    k := 0;
    for r in Filtered(Set(F!.root), r -> F!.good[r]) do
        P := F!.reps[r];
        elts := F!.elts[r];
        A := F!.aut[r];
        Inn := Group(FS_ConjugationPerms(elts, GeneratorsOfGroup(P)), ());
        Z := List(AsSSortedList(Center(P)), z -> PositionSorted(elts, z));
        for o in OrbitsDomain(A, Z) do
            k := k + FS_NumberOfDefectZeroBlocks(Stabilizer(A, o[1]) / Inn, F!.p);
        od;
    od;
    return k;
end);

InstallMethod(FusionSystemOfGroup, "for a finite group and a prime", [IsGroup, IsPosInt], function(G, p)
    local S, AS, L, Q, C, N, hom;
    S := SylowSubgroup(G, p);
    AS := List(GeneratorsOfGroup(Normalizer(G, S)), g -> ConjugatorAutomorphismNC(S, g));
    L := [];
    for Q in List(ConjugacyClassesSubgroups(S), Representative) do
        if Q <> S then
            C := Centralizer(G, Q);
            if p^PadicValuation(Size(C), p) = Size(Center(Q)) then
                N := Normalizer(G, Q);
                hom := NaturalHomomorphismByNormalSubgroup(N, ClosureGroup(Q, C));
                if Size(PCore(ImagesSource(hom), p)) = 1 then
                    Add(L, [Q, List(GeneratorsOfGroup(N), g -> ConjugatorAutomorphismNC(Q, g))]);
                fi;
            fi;
        fi;
    od;
    return FusionSystemByAutomizers(S, AS, L);
end);
