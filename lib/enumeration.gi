# Enumeration of all saturated fusion systems on a p-group.

# Y has a strongly p-embedded subgroup, where P is a Sylow p-subgroup of Y with P <> 1:
# by [AKO, Proposition A.7] and Alperin's fusion theorem, this holds iff <N_Y(Q) | 1 <> Q <= P> < Y.
BindGlobal("FS_HasStronglyPEmbeddedSubgroup", function(Y, P)
    local M, Q;
    M := Normalizer(Y, P);
    for Q in List(ConjugacyClassesSubgroups(P), Representative) do
        if Size(Q) > 1 then
            M := ClosureGroup(M, Normalizer(Y, Q));
            if Size(M) = Size(Y) then
                return false;
            fi;
        fi;
    od;
    return Size(M) < Size(Y);
end);

# lists of automorphisms of S generating a complement C to Inn(S) in Aut_F(S), for the p'-subgroups C
# of Out(S) up to conjugacy
BindGlobal("FS_AutFSChoices", function(S, nice, InnP, hom)
    local p, OutP, cand, reps, C, comp;
    p := PrimePGroup(S);
    OutP := Image(hom);
    if Size(OutP) = p^PadicValuation(Size(OutP), p) then
        return [[]];
    fi;
    if IsSolvableGroup(OutP) then
        cand := HallSubgroup(OutP, Difference(PrimeDivisors(Size(OutP)), [p]));
        cand := List(ConjugacyClassesSubgroups(cand), Representative);
    else
        cand := Filtered(List(ConjugacyClassesSubgroups(OutP), Representative), C -> Size(C) mod p <> 0);
    fi;
    reps := [];
    for C in cand do
        if ForAll(reps, D -> Size(D) <> Size(C) or not IsConjugate(OutP, C, D)) then
            Add(reps, C);
        fi;
    od;
    return List(reps, function(C)
        comp := ComplementClassesRepresentatives(PreImage(hom, C), InnP)[1];
        return List(GeneratorsOfGroup(comp), x -> PreImagesRepresentative(nice, x));
    end);
end);

InstallMethod(EssentialAutomizerCandidates, "for a p-group, a subgroup and a list of automorphisms",
    [IsPGroup, IsPGroup, IsList], function(S, E, AS)
    local p, AutE, niceE, AE, InnE, AutSE, hom, OutE, OutSE, ASgrp, stab, OutBE, N, res, Y0, g, Y, X, isnormal;
    p := PrimePGroup(S);
    AutE := AutomorphismGroup(E);
    niceE := NiceMonomorphism(AutE);
    AE := Image(niceE);
    InnE := Image(niceE, InnerAutomorphismsAutomorphismGroup(AutE));
    AutSE := Group(List(GeneratorsOfGroup(Normalizer(S, E)), n -> Image(niceE, ConjugatorAutomorphismNC(E, n))), One(AE));
    if Size(Intersection(AutSE, PCore(AE, p))) <> Size(InnE) then
        return [];
    fi;
    hom := NaturalHomomorphismByNormalSubgroup(AE, InnE);
    OutE := Image(hom);
    OutSE := Image(hom, AutSE);
    # restrictions of the stabilizer of E in Aut_F(S)
    ASgrp := Group(Concatenation(AS, List(GeneratorsOfGroup(S), s -> ConjugatorAutomorphismNC(S, s))), IdentityMapping(S));
    stab := Stabilizer(ASgrp, E, function(Q, a) return Image(a, Q); end);
    OutBE := Group(List(GeneratorsOfGroup(stab), a -> Image(hom, Image(niceE,
                 GroupHomomorphismByImagesNC(E, E, GeneratorsOfGroup(E), List(GeneratorsOfGroup(E), x -> Image(a, x)))))),
             One(OutE));
    if PadicValuation(Size(OutBE), p) > PadicValuation(Size(OutSE), p) then
        return [];
    fi;
    isnormal := Size(Normalizer(S, E)) = Size(S);
    N := Normalizer(OutE, OutSE);
    res := [];
    for Y0 in List(ConjugacyClassesSubgroups(OutE), Representative) do
        if PadicValuation(Size(Y0), p) = PadicValuation(Size(OutSE), p) and Size(Y0) mod Size(OutBE) = 0 then
            g := RepresentativeAction(OutE, SylowSubgroup(Y0, p), OutSE);
            if g <> fail then
                # all conjugates of Y0 with Sylow p-subgroup Out_S(E)
                for Y in Orbit(N, Y0^g, OnPoints) do
                    # if N_S(E) = S, every element of N_Y(Out_S(E)) extends to S by receptivity
                    if IsSubset(Y, OutBE) and Size(PCore(Y, p)) = 1 and
                       (not isnormal or Size(Normalizer(Y, OutSE)) = Size(OutBE)) and
                       FS_HasStronglyPEmbeddedSubgroup(Y, OutSE) then
                        X := Group(List(GeneratorsOfGroup(PreImage(hom, Y)), x -> PreImagesRepresentative(niceE, x)),
                                   IdentityMapping(E));
                        SetIsGroupOfAutomorphismsFiniteGroup(X, true);
                        SetAutomorphismDomain(X, E);
                        Add(res, X);
                    fi;
                od;
            fi;
        fi;
    od;
    return res;
end);

InstallMethod(AllSaturatedFusionSystems, "for a p-group", [IsPGroup], function(S)
    local D, AutS, nice, AutP, InnP, hom, results, AS, ASP, T, found, seen, reps, j, orbit, i, a, id, cand, E, X,
          sub, ch, F, new;
    D := FS_CentricData(S);
    AutS := AutomorphismGroup(S);
    nice := NiceMonomorphism(AutS);
    AutP := Image(nice);
    InnP := Image(nice, InnerAutomorphismsAutomorphismGroup(AutS));
    hom := NaturalHomomorphismByNormalSubgroup(AutP, InnP);
    results := [];
    for AS in FS_AutFSChoices(S, nice, InnP, hom) do
        # N_{Aut(S)}(Aut_F(S)) modulo Aut_F(S), for the isomorphism test
        ASP := Group(List(Concatenation(AS, List(GeneratorsOfGroup(S), s -> ConjugatorAutomorphismNC(S, s))),
                          x -> Image(nice, x)), One(AutP));
        T := List(RightTransversal(Normalizer(AutP, ASP), ASP), t -> PreImagesRepresentative(nice, t));
        found := [];
        # Aut_F(S)-orbits of S-classes of S-centric subgroups, representative with largest normalizer
        seen := [];
        reps := [];
        for j in [1..Length(D.reps)] do
            if not j in seen then
                orbit := [j];
                i := 1;
                while i <= Length(orbit) do
                    for a in AS do
                        id := FS_IdentifyCentricSubgroup(S, D, Image(a, D.reps[orbit[i]]));
                        if not id[1] in orbit then
                            Add(orbit, id[1]);
                        fi;
                    od;
                    i := i + 1;
                od;
                UniteSet(seen, orbit);
                Add(reps, orbit[PositionMaximum(List(orbit, k -> Size(D.norm[k])))]);
            fi;
        od;
        cand := [];
        for j in reps do
            E := D.reps[j];
            if E <> S and not IsCyclic(E) then
                X := EssentialAutomizerCandidates(S, E, AS);
                if X <> [] then
                    Add(cand, X);
                fi;
            fi;
        od;
        Info(InfoFusion, 1, "Aut_F(S)/Inn(S) of order ", Size(Group(AS, IdentityMapping(S))), ": ",
             List(cand, Length), " automizer candidates");
        for sub in Combinations([1..Length(cand)]) do
            for ch in Cartesian(List(sub, i -> [1..Length(cand[i])])) do
                F := FusionSystemByAutomizers(S, AS, List([1..Length(sub)], i -> cand[sub[i]][ch[i]]));
                if IsSaturatedFusionSystem(F) then
                    new := [NumberOfCharactersOfFusionSystem(F),
                            SortedList(List(CentricSubgroupClassRepresentatives(F),
                                            Q -> [Size(Q), Size(FS_AutomizerPerm(F, Q))]))];
                    if ForAll(found, x -> x[1] <> new or
                              ForAll(T, beta -> not FS_IsImageFusionSystem(x[2], F, beta))) then
                        Add(found, [new, F]);
                    fi;
                fi;
            od;
        od;
        Append(results, List(found, x -> x[2]));
    od;
    return results;
end);
