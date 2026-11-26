InstallMethod(C0Subgroups, "C subgroups", [IsPGroup], function(S)
    local p, Z0, R, I, i, E, x, C0;

    Info(InfoFusion, 1, "Finding C0");

    p := PrimePGroup(S);
    Z0 := Zed0(S);

    C0 := ClassesSolvableGroup(S, 0);
    C0 := Filtered(C0, a -> Order(a.representative) = p);
    C0 := Filtered(C0, a -> a.centralizer <> S);

    I := [];
    for i in [1..Length(C0)] do 
        E := C0[i].centralizer;
        x := C0[i].representative;
        if not IsSubset(E, Z0) then 
            if Index(Normalizer(S,E), E) = p then 
                Add(I, i);
            fi;
        else 
            Add(I, i);
        fi;
    od;

    C0 := List(I, i -> C0[i].centralizer);
    C0 := Orbits(S, C0);
    C0 := List(C0, Representative);
    Info(InfoFusion, 2, Length(C0), " proper subgroup(s) up to S-conjugacy passing Zed0Test");
    
    Info(InfoFusion, 2, "Checking proto-essential(s)");
    C0 := Filtered(C0, E -> IsProtoEssentialNC(S,E));

    return C0;
end);

# TODO: Accommodate for:
# - not checking Aut(S)-conjugates of certain subgroups
InstallGlobalFunction(MainProtoEssentials,  function(arg...)
    local   S, # the group
            Z0, # Zed0(S)
            onlyOne, # whether to only check the top iteration
            p, # the prime
            L, # central series of S' (labelled Z_i)
            j, # final position
            q, # quotient map S/Z_i
            Q, # quotients S/Z_i
            C0, # the proto-essential subgroups in C0
            C; # the proto-essential subgroups

    S := arg[1];

    if IsAbelian(S) then 
        return [];
    fi;

    if Length(arg) > 1 then 
        onlyOne := arg[2];
        if not onlyOne in [1, 0, -1] then 
            Error("Second argument must be -1, 0 or 1");
        fi;
    else 
        onlyOne := 1;
    fi;

    Z0 := Zed0(S);
    C0 := C0Subgroups(S);
    if onlyOne = 0 then 
        return C0;
    fi;

    Info(InfoFusion, 1, "Finding C - C0");

    p := PrimePGroup(S);
    L := LowerCentralSeries(S);
    # Deals with a bug in CompositionSeriesThrough (will be fixed in v4.18)
    L := FS_CSThru(S, L);
    
    j := Position(L, DerivedSubgroup(S));
    L := L{[j+1..Length(L)-1]};
    
    q := List(L, A -> NaturalHomomorphismByNormalSubgroupNC(S,A));

    Q := List(q, Image);
    C := List(Q, A -> ClassesSolvableGroup(A,0));
    C := List([1..Length(C)], i -> Filtered(C[i], a ->  Order(a.representative) = p and a.centralizer <> Q[i]));

    C := List(C, A -> List(A, a -> a.centralizer));
    C := List([1..Length(C)], i -> List(C[i], A -> PreImage(q[i], A)));

    C := Flat(C);
    C := Filtered(C, A -> IsSubset(A, Z0));
    
    C := Orbits(S, C);
    C := List(C, Representative);

    C := Filtered(C, A -> ForAll(C0, B -> not IsConjugate(S, A, B)));
    Info(InfoFusion, 2, Length(C), " proper subgroup(s) up to S-conjugacy passing Zed0Test");
    
    Info(InfoFusion, 2, "Checking proto-essential(s)");
    C := Filtered(C, E -> IsProtoEssentialNC(S,E));

    if onlyOne = 1 then 
        C := Flat([C0, C]);
    fi;

    return C;
end);

InstallMethod(GenerateProtoEssentials, "method to generate proto-essentials using the main proto-essentials", 
    [IsPGroup, IsList], function(S, L)
    local   I, # the conjugates of essentials already considered
            J, # the conjugates of essentials that still need to be considered
            AutS, # Aut(S)
            i,
            n, # some nice monomorphism
            L0, # the Aut(S)-conjugates of essentials
            j, # position of the current essential
            E, # current essential
            T, # the proto-essentials
            N, # the normal subgroups of S
            A0, # the conjugates of E
            A0F, # the current conjugates of E
            A, # the larger proto-essentials containing E
            K, # the valid choices in A
            F, # an element in A
            E0, # some Aut(S)-conjugate of E contained inside F
            AutF; # Aut(F)
            
    
    if IsEmpty(L) then 
        return L;
    fi;

    Info(InfoFusion, 1, "Generating all proto-essential subgroups from ", Length(L), " subgroups");
        
    I := [];

    # TODO: Compute all $\Aut(S)$-conjugates of subs in $L$, then take a $S$-representative
    AutS := AutomorphismGroup(S);
    n := NiceMonomorphism(AutS);
    AutS := Image(n, AutS);
    L0 := Orbits(AutS, L, OnImageNM(n));
    L0 := List(L0, A -> List(Orbits(S,  A), Representative));
    L0 := Flat(L0);

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
        K := PositionsProperty(A, X -> X <> fail);

        for i in K do
            E0 := (T[i])^((A[i][2])^-1);

            AutF := AutomorphismGroup(E0);
            n := NiceMonomorphism(AutF);
            AutF := NiceObject(AutF);
            
            # Find Aut(F)-conjugates of subgroups in A0 that are not already present (up to Aut(S)-conjugacy)
            A0F := Orbit(AutF, E, OnImageNM(n));
            A0F := Orbits(S, A0F);
            A0F := Filtered(A0F, X -> ForAll(A0, Y -> not Y in X));
            A0F := List(A0F, Representative);
            Append(A0, A0F);
        od;

        A0 := Filtered(A0, X -> ForAll(L0, Y -> not IsConjugate(S, X, Y)));
        Append(L0, A0);

        if E in L or IsProtoEssential(S, E) then 
            Add(T, E);
        fi;
    od;
    Info(InfoFusion, 1, "Generated ", Length(T), " subgroups");

    return T;
end);

InstallMethod(AllProtoEssentials, "generic method", [IsPGroup],
function(S)
    local L;

    L := MainProtoEssentials(S);
    L := GenerateProtoEssentials(S, L);

    return L;
end );
