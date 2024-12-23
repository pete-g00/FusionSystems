# computes the restrictions of automorphisms on B coming from the F-Class C,
# where a representative A of C has automizer AutFA. We build on the current automizer AutFB
AutFA := function(C, B, AutA, AutB)
    local L, M, i, Co, A, X, m, AutFO, Im, t, Aut;

    # for this class of essential subgroup C and AutA
    # find all subs conjugate to B s.t. they lie in an Aut_F(S)-conjugate of C
    # add the automizers for every orbit
    L := Reps(B);
    M := B!.R.maps;
    
    Info(InfoFusion, 1, "Given automizer has ", Length(GeneratorsOfGroup(AutA)), " generators");

    for i in [1..Length(L)] do 
        Co := ContainingFConjugates(C, L[i]);
        Info(InfoFusion, 1, "Have ", Length(Co), " F-conjugates containing A");
        for A in Co do 
            X := A[1];
            m := A[2];

            AutFO := OnAutGroupConjugation(AutA, m);
            Im := Automizer(Image(m), Image(m));
            Aut := Automizer(ClosureGroup(AutFO, Im), L[i]);
            Aut := OnAutGroupConjugation(Aut, InverseGeneralMapping(M[i]));
            Info(InfoFusion, 1, "Induced automizer has ", Length(GeneratorsOfGroup(Aut)), " generators");
            AutB := ClosureGroup(AutB, Aut);
        od;
    od;
    
    return AutB;
end;

FAutomizer := function(C, d)
    local A, Aut, T;

    A := Representative(C);
    Aut := Automizer(A,A);

    for T in d!.entries do 
        Aut := AutFA(T[1], C, T[2], Aut);
    od;

    SetIsGroupOfAutomorphisms(Aut, true);
    return Aut;
end;

# TODO: Add nocheck, that guarantees that no essential subgroup is a subgroup of another
InstallMethod(SaturatedFusionSystem, "for a group and a list of automorphisms",
    [IsGroup, IsList],
    function(S, L)
        local p, SGens, AutFS, B, G, f, Sf, d, E, X, R, C, Aut, I, cmaps, L0, AutFX;

        p := FindPrimeOfPrimePower(Size(S));
        Assert(0, p <> fail);

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
        AddDictionary(d, Sf, ClosureGroup(Automizer(S,S),B));

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
            Aut := FAutomizer(C, d);
            
            I := Filtered([1..Length(L)], i -> Source(L[i]) in C);
            cmaps := List(I, i -> FindMap(C, Source(L[i])));
            # conjugate hom[i] with ms[i]
            # construct the closure of Aut_F(S)
            # add it to the dictionary d
            L0 := List([1..Length(I)], i -> OnHomConjugation(L[I[i]], InverseGeneralMapping(cmaps[i])));
            AutFX := ClosureGroup(Aut, Group(L0));
            AddDictionary(d, C, AutFX);

            L := L{Difference([1..Length(L)], I)};
        od;

        return Objectify(NewType(FusionSystemFamily, IsSaturatedFusionSystemRep),
                rec(G := G, f := f, p := p, S := S, d := d));
    end );

InstallMethod(UnderlyingGroup, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        return F!.S;
    end );

InstallMethod(Prime, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        return F!.p;
    end );

InstallMethod(AutF, "for a saturated fusion system and a subgroup",
    [IsSaturatedFusionSystemRep, IsGroup],
    function(F,A)
        local C, d;

        C := FClass(F,A);
        d := F!.d;
        
        return FAutomizer(C,d);
    end );

InstallMethod(RepresentativeFIsomorphism, "for a saturated fusion system and subgroups",
    [IsSaturatedFusionSystemRep, IsGroup, IsGroup],
    function(F, A, B)
        return FindMap(FClass(F,A), B);
    end );

InstallMethod(FClasses, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        local S, C, L, A;

        S := UnderlyingGroup(F);
        C := ConjugacyClassesSubgroups(S);
        C := List(C, Representative);
        # Group up to Aut-F class
        
        L := [];
        for A in C do 
            # TODO: Only check by size/group id
            if ForAll(L, X -> not A in X) then 
                Info(InfoFusion, 1, "New class of order ", Size(A));
                Add(L, FClass(F,A));
            fi;
        od;

        return L;
    end );

InstallMethod(Core, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep], 
    function(F)
        local E, N, A, R, n;

        E := F!.d!.entries;
        N := NormalSubgroups(UnderlyingGroup(F));
        for A in E do 
            R := Representative(A[1]);
            N := Filtered(N, X -> IsSubset(R, X) and IsNormal(R, X));
            N := Orbits(A[2], N, OnImage);
            N := Filtered(N, X -> Size(X) = 1);
            N := List(N, Representative);
        od;

        n := Maximum(List(N, Size));
        return First(N, A -> Size(A) = n);
    end );

InstallMethod(FocalSubgroup, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        local T, E, A, R, Aut, T0;

        T := TrivialSubgroup(UnderlyingGroup(F));
        E := F!.d!.entries;
        
        for A in E do 
            R := Representative(A[1]);
            Aut := A[2];
            T0 := List(GeneratorsOfGroup(Aut), alpha -> List(GeneratorsOfGroup(R), x -> x^-1*Image(alpha,x)));
            T := ClosureGroup(T, Flat(T0));
        od;

        return T;
    end );

InstallMethod(IsReduced, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        return IsTrivial(Core(F)) and FocalSubgroup(F) = UnderlyingGroup(F);
    end );

Foc := function(S, L)
    local T, A, X, T0;

    T := TrivialSubgroup(S);
    for A in L do 
        X := Source(Identity(A));
        T0 := List(GeneratorsOfGroup(A), alpha -> List(GeneratorsOfGroup(X), x -> x^-1*Image(alpha, x)));
        T := ClosureGroup(T, Flat(T0));
    od;

    return T;
end;
