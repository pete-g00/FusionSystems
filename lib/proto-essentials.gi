InstallMethod(IsProtoEssential, "method to check whether a subgroup is proto-essential", 
    [IsPGroup, IsPGroup], function(S, E)
    local i;

    if S = E or not IsSubset(E, Centralizer(S,E)) then 
        return false;
    fi;

    if not PE_FrattiniTest(S, E) then 
        return false;
    fi;

    i := PE_RankTest(S, E);
    if i=-1 then 
        return false;
    fi;

    if not PE_LiftTest(S, E, i) then 
        return false;
    fi;

    if not PE_RadicalTest(S, E, i) then 
        return false;
    fi;

    return PE_InvolutionsConjugate(S, E, i);
end);

# TODO: Accommodate for:
# - not checking Aut(S)-conjugates of certain subgroups
InstallGlobalFunction(MainProtoEssentials,  function(arg...)
    local   S, # the group
            onlyOne, # whether to only check the top iteration
            p, # the prime
            G, # holomorph of S
            i, # Embedding of S to G
            S0, # Image of S in G
            L, # central series of S' (labelled Z_i)
            j, # final position
            q, # quotient map S/Z_i
            Q, # quotients S/Z_i
            C; # the proto-essential subgroups

    S := arg[1];

    if Length(arg) > 1 then 
        onlyOne := arg[2];
    else 
        onlyOne := false;
    fi;

    if IsAbelian(S) then 
        return [];
    fi;

    p := PrimePGroup(S);

    if not onlyOne then 
        L := LowerCentralSeries(S);
        # Deals with a bug in CompositionSeriesThrough (will be fixed in v4.18)
        L := CSThru(S, L);
        
        j := Position(L, DerivedSubgroup(S));
        L := L{[j+1..Length(L)]};
        Info(InfoFusion, 1, Length(L), " iterations");
        
        q := List(L, A -> NaturalHomomorphismByNormalSubgroup(S,A));

        Info(InfoFusion, 1, "Finding conjugacy classes");
        
        Q := List(q, Image);
        C := List(Q, A -> ClassesSolvableGroup(A,0));
        C := List(C, A -> Filtered(A, a -> Order(a.representative) = p));
        C := List(C, A -> List(A, a -> a.centralizer));
        C := List([1..Length(C)], i -> List(C[i], A -> PreImage(q[i], A)));
        C := Flat(C);
    else 
        Info(InfoFusion, 1, "Only the top iteration");
        Info(InfoFusion, 1, "Finding conjugacy classes");

        C := ClassesSolvableGroup(S, 0);
        C := Filtered(C, a -> Order(a.representative) = p);
        C := List(C, a -> a.centralizer);
    fi;

    Info(InfoFusion, 1, Length(C), " subgroups, including possibly duplicates");
    Info(InfoFusion, 2, "\tFinding S-reps");

    C := Orbits(S, C);
    Info(InfoFusion, 1, Length(C), " up to S-conjugacy");

    C := List(C, Representative);
    
    Info(InfoFusion, 1, "Checking proto-essentials");
    C := Filtered(C, E -> IsProtoEssential(S,E));

    return C;
end);

InstallMethod(GenerateProtoEssentials, "method to generate proto-essentials using the main proto-essentials", 
    [IsPGroup, IsList], function(S, L)
    local   G, # holomorph of S
            i, # Embedding of S to G
            S0, # Image of S in G
            I, # the conjugates of essentials already considered
            J, # the conjugates of essentials that still need to be considered
            L0, # the conjugates of essentials
            j, # position of the current essential
            E, # current essential
            T, # the proto-essentials
            N, # the normal subgroups of S
            A0, # the conjugates of E
            A0F, # the current conjugates of E
            A, # the larger proto-essentials containing E
            F, # an element in A
            E0, # some Aut(S)-conjugate of E contained inside F
            AutF, # Aut(F)
            n; # nice monomorphism for Aut(F)
    
    if IsEmpty(L) then 
        return L;
    fi;

    Info(InfoFusion, 1, "Generating all proto-essential subgroups");
    I := [];
    L0 := ShallowCopy(L);
    T := [];

    while Length(I) <> Length(L0) do 
        # we're dealing with some subgroup of largest order not yet considered
        J := Difference([1..Length(L0)], I);
        j := PositionMaximum(List(L0{J}, Size));
        j := J[j];
        E := L0[j];
        Add(I, j);

        A0 := [E]; 
        A := List(T, X -> ContainedConjugates(S, X, E, true));
        A := Filtered(A, X -> X <> fail);

        for F in A do
            E0 := E^(F[2]);

            AutF := AutomorphismGroup(F[1]);
            n := NiceMonomorphism(AutF);
            AutF := NiceObject(AutF);
            
            # Find Aut(F)-conjugates of subgroups in A0 that are not already present (up to Aut(S)-conjugacy)
            A0F := Orbit(AutF, E0, OnImageNM(n));
            A0F := Orbits(S, A0F);
            A0F := Filtered(A0F, X -> ForAll(A0, Y -> not Y in X));
            A0F := List(A0F, Representative);
            Append(A0, A0F);
        od;

        A0 := Filtered(A0, X -> ForAll(L0, Y -> not IsConjugate(S, X, Y)));
        Append(L0, A0);

        if E in L0 or IsProtoEssential(S0, E) then 
            Add(T, E);
        fi;
    od;

    return T;
end);

InstallMethod(AllProtoEssentials, "method to find all proto-essentials", [IsPGroup], function(S)
    local L;

    # TODO: Use the other algorithm for those with q-pearls
    # TODO: Deal with the case when $S$ has class <= 2 (without computing $\Aut(S)$)

    L := MainProtoEssentials(S);
    L := GenerateProtoEssentials(S, L);

    return L;
end);
