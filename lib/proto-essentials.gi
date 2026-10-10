FrattiniTest := function(S, P)
    local ucs, FP, Theta, g;

    ucs := Reversed(UpperCentralSeries(P));
    FP := FrattiniSubgroup(P);
    for Theta in ucs{[1..Minimum(2,Length(ucs))]} do 
        for g in RightTransversal(Normalizer(S,P),P) do
            if g in P then 
                continue; 
            fi;
            if IsSubgroup(ClosureGroup(Theta,FP), CommutatorSubgroup(Group(g),P))
                    and IsSubgroup(FP, CommutatorSubgroup(Group(g), Theta)) then
                return false;
            fi;
        od;   
    od;
    return true;
end;

LargeRankTest := function(S,P)
    local FP,NSP,k,l,s,sP;

    FP := FrattiniSubgroup(P);
    NSP := Normalizer(S,P); 

    k := PValuation(IndexNC(NSP, P), 2);
    l := Rank(P);

    if k >= 2 then
        # Note [s,P/Phi(P)] = [s,P]Phi(P)/Phi(P), and we can check the
        # inequality for s in a transversal to P in N_S(P), because for
        # each s in P, we have [s,Phi(P)] \leq Phi(P). 
        for s in RightTransversal(NSP,P) do
            if s in P then continue; fi;
            sP := CommutatorSubgroup(Group(s),P); 
            # Since [s,P]Phi(P)/Phi(P) is elementary abelian, to require
            # its rank \geq 2 is the same as requiring its order \geq 4. 
            if IndexNC(sP, Intersection(sP,FP)) < 4 then
                return false;
            fi;
        od;
    fi;

    return true;
end;

InstallMethod(PE_FAST2, "method to check whether E is proto-essential in S (fast)", 
    [IsPGroup, IsPGroup], function(S, E)
    local N, OutSE, i, A;

    N := Normalizer(S, E);
    # Out_S(E) must be: cyclic (order 2,4,8), quaternion (order 8) or eab (order 4, 8)
    if Index(N, E) > 8 then 
        Info(InfoFusion, 2, "\t(iii) \\Out_S(E) has order > 8");
        return false;
    elif Index(N, E) = 8 and IdGroup(N/E)[2] in [2,3] then 
        Info(InfoFusion, 2, "\t(iii) \\Out_S(E) invalid of order 8");
        return false;
    fi;

    if Size(E) <= 2^8 then 
        N := Normalizer(S, E);
        OutSE := N/E;
        i := IdGroup(OutSE);
        if not IdGroup(E) in ValidChoices!.(i[1])!.(i[2]) then 
            Info(InfoFusion, 2, "\t(iv) E invalid for given \\Out_S(E)");
            return false;
        fi;
    fi;
    
    if not FrattiniTest(S, E) then 
        Info(InfoFusion, 2, "\t(v) Failed Frattini Test");
        return false;
    elif not LargeRankTest(S, E) then 
        Info(InfoFusion, 2, "\t(vi) Failed rank test");
        return false;
    fi;

    # order 2^9: only look at init aut-grp - check Syl-2 is not normal here
    A := InitAutomorphismGroupOver(E);
    # if A is a 2-group, then Aut(E) is also a 2-group
    if A.size = 1 or (IsPrimePowerInt(A.size) and SmallestRootInt(A.size) = 2) then
        Info(InfoFusion, 2, "\t(vii) Aut_0(E) 2-group");
        return false;
    fi;

    return true;
end);

InstallMethod(PE_SLOW2, "method to check whether E is proto-essential in S (slow)", 
    [IsPGroup, IsPGroup], function(S, E)
    local AutE, OutSE, AutSE, AutE_c, InnE, OutE, Aut2, N, C, n, q, A;

    AutE := AutomorphismGroupPGroup(E);
    OutSE := Normalizer(S,E)/E;
    
    if IsPrimePowerInt(AutE.size) then 
        Info(InfoFusion, 2, "\t(viii) Aut(E) is a 2-group");
        return false;
    fi;

    AutSE := Automizer(S, E);

    if AutE.glOrder = 1 then 
        Info(InfoFusion, 3, "\tAut(E) is solvable");

        AutE_c := ConvertHybridAutGroup(AutE);
        SetAutomorphismGroup(E, AutE_c);
        SetIsGroupOfAutomorphismsFiniteGroup(AutE_c, true);
        AutE := PcGroupAutPGroup(AutE);
        InnE := InnerAutGroupPGroup(AutE);
        AutSE := PcSubAutPGroup(AutE, AutSE);
    else 
        Info(InfoFusion, 3, "\tAut(E) is not solvable");
        AutE := ConvertHybridAutGroup(AutE);
        
        if not IsAbelian(E) then 
            InnE := InnerAutomorphismGroup(E);
        else 
            InnE := TrivialSubgroup(AutE);
        fi;

        SetIsGroupOfAutomorphismsFiniteGroup(AutE, true);
        n := NiceMonomorphism(AutE);
        SetAutomorphismGroup(E, AutE);
        SetNiceMonomorphism(AutE, n);

        AutE := Image(n, AutE);
        InnE := Image(n, InnE);
        AutSE := Image(n, AutSE);
    fi;

    if Size(OutSE) > 2 and IsElementaryAbelian(OutSE) then 
        N := Normalizer(AutE, AutSE);
        if Size(N) mod (Size(OutSE)-1) <> 0 then 
            Info(InfoFusion, 2, "\t(ix) N_{\\Out(E)}(\\Out_S(E)) does not have an element permuting the involutions transitively");
            return false;
        fi;
    fi;

    # radical test
    Aut2 := PCore(AutE, 2);
    if Size(Intersection(Aut2, AutSE)) <> IndexNC(E, Center(E)) then
        Info(InfoFusion, 2, "\t(x) E is not S-radical");
        return false;
    fi;

    # involution conjugate test
    q := NaturalHomomorphismByNormalSubgroupNC(AutE, InnE);
    OutE := Image(q);
    OutSE := Image(q, AutSE);

    if Size(OutSE) > 2 and IsElementaryAbelian(OutSE) then 
        N := Normalizer(OutE, OutSE);
        C := Centralizer(OutE, OutSE);
        if IndexNC(N, C) mod (Size(OutSE)-1) <> 0 then 
            Info(InfoFusion, 2, "\t(xi) N_{\\Out(E)}(\\Out_S(E)) does not have an element permuting the involutions transitively");
            return false;
        fi;
        # lift check -- the element of order 2^a - 1 must lift to N_S(E)
        N := Normalizer(S, E);
        A := AutomorphismGroup(N);
        if Size(A) mod (Size(OutSE)-1) <> 0 then 
            Info(InfoFusion, 3, "\t(xi) The map permuting involutions transitively cannot lift to N_S(E)");
            return false;
        fi;
    fi;

    return true;
end );

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

InstallMethod(AllProtoEssentials, "generic method", [IsPGroup],
function(S)
    local L;

    L := MainProtoEssentials(S);
    L := GenerateProtoEssentials(S, L);

    return L;
end );
