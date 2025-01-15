HasOrderP2 := function(S)
    return not (IsCyclic(S) or IsQuaternionGroup(S));
end;

IsPearl := function(A, p)
    return 
        (Size(A) = p^2 and IsElementaryAbelian(A))
    or 
        (Size(A) = p^3 and not IsAbelian(A) and Exponent(A) = p);
end;

IsMaximalClass := function(A, p)
    local n;

    n := PValuation(Size(A), p);
    return NilpotencyClassOfGroup(A) = n-1;
end;

# Finds the proto-essential subgroups of S (up to Aut(S)-cocl)
ProtoEssentialSubgroups := function(S, p)
    local IsCentric, AutS, C, n;
    
    IsCentric := function(S, E)
        return IsSubset(E, Centralizer(S, E));
    end;
    
    Info(InfoFusion, 1, "Find proto-essential subgroups of S");
    
    n := PValuation(Size(S), p);
    Assert(0, n <> fail);

    Info(InfoFusion, 3, "Finding the subgroups of S");
    C := ConjugacyClassesSubgroups(S);
    Info(InfoFusion, 3, "There are ", Length(C), " subgroups up to conjugacy");

    # no cyclic subgroups can be proto-essential
    Info(InfoFusion, 3, "Removing cyclic subgroups");
    C := Filtered(C, x -> not IsCyclic(Representative(x)) and Representative(x) <> S);
    Info(InfoFusion, 3, "There are ", Length(C), " subgroups up to conjugacy");

    # if not maximal class, E must not be a pearl
    if NilpotencyClassOfGroup(S) <> n-1 then 
        Info(InfoFusion, 3, "Removing pearls");
        C := Filtered(C, x -> not IsPearl(Representative(x), p));
        Info(InfoFusion, 3, "There are ", Length(C), " subgroups up to conjugacy");
    fi;
    
    # E cannot be maximal class if >= p^4 
    Info(InfoFusion, 3, "Removing maximal class (>= p^4)");
    C := Filtered(C, x -> Size(Representative(x)) < p^4 or not IsMaximalClass(Representative(x), p));
    Info(InfoFusion, 3, "There are ", Length(C), " subgroups up to conjugacy");
    
    # E must be S-centric
    Info(InfoFusion, 3, "Filtering S-centric subgroups");
    C := Filtered(C, x -> IsCentric(S, Representative(x)));
    Info(InfoFusion, 3, "There are ", Length(C), " subgroups up to conjugacy");

    # if E has rank r, then |Out_P(E)| <= p^(floor(r/2))
    Info(InfoFusion, 3, "Removing rank r with |N_S(E) : E|^2 > p^r");
    C := Filtered(C, x -> Index(Normalizer(S, Representative(x)), Representative(x))^2 <= p^(Rank(Representative(x))));
    Info(InfoFusion, 3, "There are ", Length(C), " subgroups up to conjugacy");
    
    AutS := AutomorphismGroup(S);
    if not HasNiceMonomorphism(AutS) then 
        AssignNiceMonomorphismAutomorphismGroup(AutS, S);
    fi;
    n := NiceMonomorphism(AutS);
    
    Info(InfoFusion, 3, "Grouping up to Aut-cocl");
    C := Orbits(Image(n,AutS), C, OnCoClNM(S,n));
    Info(InfoFusion, 3, "There are ", Length(C), " subgroups up to Aut-conjugacy");

    return List(C, A -> Representative(Representative(A)));
end;

# finds potential automizers for a proto-essential subgroup
PotentialAutomizers := function(S, E, p)
    local AutE, n, AutEp, AutSE, InnE, A, C, L, I;

    Info(InfoFusion, 3, "Finding automorphism group of E");
    AutE := AutomorphismGroup(E);
    
    Info(InfoFusion, 3, "Finding nice monomorphism for Aut(E)");
    if not HasNiceMonomorphism(AutE) then 
        AssignNiceMonomorphismAutomorphismGroup(AutE, E);
    fi;
    n := NiceMonomorphism(AutE);

    AutE := Image(n, AutE);
    AutEp := PCore(AutE, p);

    AutSE := Automizer(S, E);
    AutSE := Image(n, AutSE);

    InnE := Automizer(E, E);
    InnE := Image(n, InnE);

    # E has to be radical, i.e. Out_S(E) \cap O_p(Out(E)) = 1
    if Size(Intersection(AutEp, AutSE)) <> IndexNC(E, Center(E)) then 
        Info(InfoFusion, 3, "E cannot be radical");
        return fail;
    fi;
    Info(InfoFusion, 3, "E can be radical");

    A := ComplementClassesRepresentatives(AutE, AutEp);
    Assert(0, Length(A) = 1);
    A := A[1];
    Info(InfoFusion, 3, "The complement has order ", Size(A));

    C := ConjugacyClassesSubgroups(A);
    Info(InfoFusion, 3, "There are ", Length(C), " subgroups of the complement");
    
    C := List(C, Representative);
    C := Filtered(C, X -> Size(SylowSubgroup(X,p)) = IndexNC(Normalizer(S,E), E) and HasStronglyPEmbeddedSubgroup(X, p) and PResidue(X,p) = X);
    Info(InfoFusion, 3, " of which ", Length(C), " have a strongly p-embedded subgroup (up to p-residue)");
    C := List(C, X -> ClosureGroup(InnE, X));

    L := List(C, AutFE -> ContainedConjugates(AutE, AutFE, AutSE, true));
    I := Filtered([1..Length(L)], i -> L[i] <> fail);
    Info(InfoFusion, 3, " of which ", Length(L), " contain(s) Aut_S(E)");
    
    L := List(I, i -> C[i]^(L[i][2]^-1));

    return List(L, X -> PreImage(n, X));
end;

# initializes an automizer of E, in particular the maximum NPhi
InitializeAutomizer := function(S, E, AutFE, p)
    local AutE, n, AutSE, D;

    AutE := AutomorphismGroup(E);
    n := NiceMonomorphism(AutE);

    AutSE := Automizer(S, E);
    AutSE := Image(n, AutSE);

    D := FindMaxNPhi(S, AutFE);
    D := Image(n, D);

    return rec(
        AutFE := Image(n, AutFE),
        AutSE := AutSE,
        n := n,
        N := Normalizer(Image(n,AutE), AutSE),
        D := D
    );
end;

# Finds an automizer with respect to some Borel complement
FindValidAutomizer := function(S, B, nS, E, R, p)
    local AutS, n, E0, x, B0, C, g, AutFE, A;

    AutS := AutomorphismGroup(S);
    if not HasNiceMonomorphism(AutS) then 
        AssignNiceMonomorphismAutomorphismGroup(AutS, S);
    fi;
    n := NiceMonomorphism(AutS);

    # E0 := AutomorphismDomain(Source(R.n));
    # x := RepresentativeAction(Image(n,AutS), E, E0, OnImageNM(n));
    # Assert(0, x <> fail);

    B0 := Automizer(B, E);
    # B0 := OnAutGroupConjugation(B0, PreImagesRepresentative(nS,x));
    B0 := ClosureGroup(R.AutSE, Image(R.n, B0));

    C := ContainedConjugates(R.N, B0, R.D, true);

    if C = fail then return fail; fi;
    
    g := C[2];
    AutFE := R.AutFE^g;
    A := ClosureGroup(AutFE, B0);
    
    # fully automized
    if IndexNC(A, R.AutSE) mod p = 0 then
        return fail;
    fi;

    # invalid PResidue
    if PResidue(A, p) <> AutFE then
        return fail;
    fi;

    return PreImage(R.n, A);

    # return OnAutGroupConjugation(PreImage(R.n, A), PreImagesRepresentative(nS,x)^-1);
end;

# Finds the Borel complements
BorelComplements := function(S, p)
    local AutS, n, B, C, L, i, X;

    Info(InfoFusion, 1, "Finding all possible Borel complements");

    AutS := AutomorphismGroup(S);
    n := NiceMonomorphism(AutS);
    AutS := Image(n,AutS);
    Assert(0, IsSolvable(AutS));

    B := SylowComplement(AutS, p);
    Info(InfoFusion, 1, "The maximal Borel complement has order ", Size(B));
    C := ConjugacyClassesSubgroups(B);
    
    L := [];
    for X in C do 
        if ForAll(L, A -> IsomType(Representative(X)) <> IsomType(A) or Representative(X)^AutS <> A^AutS) then 
            Add(L, Representative(X));
        fi;
    od;
    Info(InfoFusion, 1, "There are ", Length(L), " distinct complements");
    
    return List(L, A -> PreImage(n, A));
end;

# Checks whether the combination of automizers (A: the Borel complement, L: the list of automizers) could be reduced
IsPotentiallyReduced := function(S, A, L)
    local N, T, i, A0, E, n, T0;

    N := NormalSubgroups(S);
    T := TrivialSubgroup(S);
    
    for i in [0..Length(L)] do
        if i = 0 then 
            A0 := A;
        else 
            A0 := L[i];
        fi;
        E := AutomorphismDomain(A0);
        N := Filtered(N, X -> IsSubset(E, X) and IsNormal(E, X));
        
        if not HasNiceMonomorphism(A0) then 
            AssignNiceMonomorphismAutomorphismGroup(A0, E);
        fi;
        n := NiceMonomorphism(A0);

        # find those subgroups fixed by Aut_F(E)
        N := Orbits(Image(n,A0), N, OnImageNM(n));
        N := Filtered(N, X -> Size(X) = 1);
        N := List(N, Representative);

        # construct residue
        T0 := List(GeneratorsOfGroup(A0), alpha -> List(GeneratorsOfGroup(E), x -> x^-1*Image(alpha,x)));
        T := ClosureGroup(T, Flat(T0));
    od;

    return Length(N) = 1 and T = S;
end;

ShallowFlat := function(L) 
    local D, A;

    D := [];

    for A in L do 
        Append(D, A);
    od;

    return D;
end;

# TODO: NOT COMPLETED
# Generates automizers 
GenerateAutomizers := function(O, C, n, AutList)
    local Aut, i, j, g;

    Aut := [];

    for i in [1..Length(C)] do 
        for j in [1..C[i]] do 
            g := PreImagesRepresentative(n, O[i][j]);
            Add(Aut, OnAutGroupConjugation(AutList[i], g));
        od;
    od;

    return Aut;
end;

# constructs some reduced fusion system
ConstructReducedFS := function(S, B, E, L, p)
    local AutS, n, N, O, Aut, I, F0, Com, T, t, Au, F, C, c, Autos;

    AutS := AutomorphismGroup(S);
    if not HasNiceMonomorphism(AutS) then 
        AssignNiceMonomorphismAutomorphismGroup(AutS, S);
    fi;
    
    n := NiceMonomorphism(AutS);
    # normalizer of the Borel complement determines isomorphism as fusion systems
    N := Normalizer(Image(n,AutS), Image(n,B));

    O := List(E, A -> Orbit(Image(n,AutS), A^S, OnCoClNM(S,n)));
    O := List(O, T -> Orbits(N, T, OnCoClNM(S,n)));
    
    # I := List(J, i -> List(I[i].Auts, A -> InitializeAutomizer(S, L[i], A, I[i].AutSE, p)));

    Aut := List([1..Length(L)], i -> List(O[i], T -> List(L[i], V -> FindValidAutomizer(S, B, n, Representative(Representative(T)), V, p))));
    Aut := ShallowFlat(Aut);
    O := ShallowFlat(O);

    Aut := List(Aut, T -> Filtered(T, A -> A <> fail));
    I := Filtered([1..Length(Aut)], i -> not IsEmpty(Aut[i]));

    Aut := Aut{I};
    O := List(I, i -> RightTransversal(Image(n,B), Stabilizer(Image(n,B), Representative(O[i]), OnCoClNM(S,n))));
    C := Cartesian(List(O, t -> [1..Size(t)]));

    F0 := [];

    Info(InfoFusion, 2, "There are ", Length(I), " possible automizer(s)");
    Info(InfoFusion, 2, " and ", List(O, Size), " conjugate(s) within the normalizer");
    Com := Combinations([1..Length(I)]);

    for t in Com{[2..Length(Com)]} do 
        Info(InfoFusion, 3, "Looking at combination ", t, " of essential subgroup(s)"); 
        T := Cartesian(Aut{t});
        for Au in T do
            Info(InfoFusion, 3, "Looking at combination of distinct automizers with sizes ", List(Au, Size));
            # take i combos of them
            for c in C do
                Info(InfoFusion, 3, "Looking at combination ", c{t}, " of active Aut_F(S)-conjugates"); 
                Autos := GenerateAutomizers(O, c{t}, n, Au); 
                Info(InfoFusion, 3, "The automizers found have order ", List(Autos, Size));
                if IsPotentiallyReduced(S, B, Autos) then
                    Add(F0, Flat([B, Autos])); 
                    # F := SaturatedFusionSystem(S, Flat([B, Aut]));
                    # if IsSaturated(F) then 
                        Info(InfoFusion, 3, "Is reduced and saturated");
                    #     Add(F0, F);
                    # fi;
                fi;
            od;
        od;
    od;

    return F0;
end;

AllReducedFusionSystems := function(S)
    local p, L, P, I, J, AutS, nS, B, F0, A;

    p := FindPrimeOfPrimePower(Size(S));
    
    L := ProtoEssentialSubgroups(S, p);
    P := List(L, E -> PotentialAutomizers(S, E, p));
    J := Filtered([1..Length(I)], i -> I[i] <> fail or IsEmpty(I[i]));

    Info(InfoFusion, 2, "There are ", Length(J), " possible essential subgroups");
    Info(InfoFusion, 2, " and potential automizers for each have size", List(I{J}, X -> List(X.Auts, Size)));

    L := L{J};
    P := P{J};

    I := List(J, i -> List(I[i].Auts, A -> InitializeAutomizer(S, L[i], A, I[i].AutSE, p)));
    # L := L{J};

    AutS := AutomorphismGroup(S);
    B := BorelComplements(S, p);

    F0 := [];

    for A in B do 
        Info(InfoFusion, 2, "Looking at automizer of size ", Size(A));
        Append(F0, ConstructReducedFS(S, A, L, I, p));
    od;

    return F0;
end;
