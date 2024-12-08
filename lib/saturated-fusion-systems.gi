InstallMethod(SaturatedFusionSystem, "for a group and a list of automorphisms",
    [IsGroup, IsList],
    function(S, L)
        local p, SGens, AutFS, B, G, f, Sf, d, E, X, R, C, I, cmaps, L0, AutFX;

        p := FindPrimeOfPrimePower(Size(S));
        SGens := Filtered(L, x -> Source(x) = S);
        AutFS := ClosureGroup(InnerAutomorphismGroup(S), SGens);

        if not IsSolvable(AutFS) then 
            Error("Aut_F(S) is not solvable.");
        fi;

        B := SylowComplement(AutFS, p);
        G := SemidirectProduct(B, S);
        f := Embedding(G,2);

        Sf := FClass(G,f,S,rec(class := [S], maps := [IdentityMapping(S)]),S);
        d := NewDictionary(Sf, true);
        AddDictionary(d, Sf, B);

        L := Filtered(L, x -> Source(x) <> S);

        if IsEmpty(L) then 
            return Objectify(NewType(FusionSystemFamily, IsSaturatedFusionSystemRep),
                rec(G := G, f := f, p := p, S := S, d := d));
        fi;
        
        # we sort to capture ALL the containment relations between the essential subgroups
        SortBy(L, x -> Size(Source(x)));

        E := [];
        while not IsEmpty(L) do 
            X := Source(L[1]);
            R := OrbitUpToClass(G, f, X, d);
            C := FClass(G, f, X, R, S);
            
            I := Filtered([1..Length(L)], i -> Source(L[i]) in C);
            cmaps := List(I, i -> FindMap(C, Source(L[i])));
            # conjugate hom[i] with ms[i]
            # construct the closure of Aut_F(S)
            # add it to the dictionary d
            L0 := List([1..Length(I)], i -> OnHomConjugation(L[I[i]], cmaps[i]));
            AutFX := Group(L0);
            AddDictionary(d, C, AutFX);

            L := L{Difference([1..Length(L)], I)};
        od;

        return Objectify(NewType(FusionSystemFamily, IsSaturatedFusionSystemRep),
                rec(G := G, f := f, p := p, S := S, d := d));
    end );

InstallMethod(UnderlyingGroup, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        return F!.G;
    end );

InstallMethod(Prime, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        return F!.p;
    end );

# DeclareOperation("RepresentativeFIsomorphism", [IsFusionSystem, IsGroup, IsGroup]);
# DeclareAttribute("FClassesReps", IsFusionSystem);

# computes the restrictions of automorphisms on B coming from the F-Class C,
# where a representative A of C has automizer AutFA. We build on the current automizer AutFB
AutFA := function(C, B, AutFA, AutFB)
    local Subs, Maps, f, G, i, T, X, A1, x, AutFX;

    Subs := Reps(C);
    Maps := C!.R.maps;
    f := C!.f;
    G := C!.G;

    for i in [1..Length(Subs)] do 
        T := Subs[i];
        C := ContainingConjugates(G, Image(f,T), Image(f,B));
        for X in C do 
            A1 := PreImage(f,X[1]);
            x := ConjugatorIsomorphism(X[1], X[2]);
            x := OnHomConjugation(x, RestrictedInverseGeneralMapping(f));;
            AutFX := OnAutGroupConjugation(AutFA, Maps[i]*x);
            AutFB := ClosureGroup(AutFB, Automizer(AutFX, B));
            AutFB := ClosureGroup(AutFB, Automizer(A1, B));
        od;
    od;

    return AutFB;
end;

InstallMethod(AutF, "for a saturated fusion system and a subgroup",
    [IsSaturatedFusionSystemRep, IsGroup],
    function(F,A)
        local d, Aut, T;

        d := F!.d;
        Aut := InnerAutomorphismGroup(A);

        for T in d!.entries do 
            Aut := AutFA(T[1], A, T[2], Aut);
        od;
        
        return Aut;
    end );
