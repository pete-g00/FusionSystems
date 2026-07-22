InstallMethod(PE_RankTest, "proto-essential rank test", [IsPGroup, IsPGroup], function(S, E)
    local   p, # the prime
            r, # the rank of E
            NSE, # N_S(E)
            n, # \Out_S(E) = p^n
            log_pr, # ceil(log_p(r))
            OutSE; # \Out_S(E)

    if IsTrivial(E) then 
        return false;
    fi;

    p := PrimePGroup(S);

    r := Rank(E);
    NSE := Normalizer(S,E);
    n := PValuation(IndexNC(NSE,E), p);

    log_pr := Int(Ceil(Log2(Float(r))/Log2(Float(p))));

    OutSE := NSE/E;

    if IsCyclic(OutSE) then 
        if PValuation(Size(OutSE), p) <= log_pr then 
            return 0;
        else 
            return -1;
        fi;
    elif IsQuaternionGroup(OutSE) then 
        if PValuation(Size(OutSE), p) <= log_pr+1 then 
            return 0;
        else 
            return -1;
        fi;
    fi;

    # PSL(2,p^n)
    if IsElementaryAbelian(OutSE) then 
        if 2*PValuation(Size(OutSE),p) <= r then 
            return 1;
        else 
            return -1;
        fi;
    fi;

    if p = 2 and Length(Set([Omega(OutSE, p, 1), Center(OutSE), FrattiniSubgroup(OutSE), DerivedSubgroup(OutSE)])) = 1 
        and 2*PValuation(Size(OutSE),2) <= r then 
        if Size(OutSE) = Size(Omega(OutSE, p, 1))^2 then 
            return 4;
        elif Size(OutSE) = Size(Omega(OutSE, p, 1))^2 then 
            return 5;
        fi;
    fi;

    if p = 3 then 
        # 3^{1+2}_-
        if Size(OutSE) = 27 and IdGroup(OutSE) = [27,4] and r >= 6 then 
            return 3;
        fi;

        # ^2 G_2(q)
        # TODO: Code this
    fi;

    # PSU(3,p^n)
    if p >= 3 and n mod 3 = 0 and Exponent(OutSE) = p and 
        Length(Set([Center(OutSE), DerivedSubgroup(OutSE), FrattiniSubgroup(OutSE)])) = 1 and 
        NilpotencyClassOfGroup(OutSE) = 2 and 
        IsElementaryAbelian(Center(OutSE)) and Size(Center(OutSE)) = p^(2*n/3) and
        HasElementaryAbelianFactorGroup(OutSE, Center(OutSE)) then 
        if r >= 6*n then 
            return 2;
        else 
            return -1;
        fi;
    fi;

    return -1;
end );

InstallMethod(PE_FrattiniTest, "proto-essential frattini test", [IsPGroup, IsPGroup], function(S, E)
    # Specific case when $C_{N_S(E)}(E/\Phi(E)) = N_S(E)$
    if CommutatorSubgroup(Normalizer(S,E), E) = FrattiniSubgroup(E) then 
        return false;
    fi;

    return CentralizerMod(Normalizer(S,E),E,FrattiniSubgroup(E)) = E;
end );

# Lifts in $\SL_2(q)$
IsProtoEssentialSubgroup_EABLiftSL2q := function(S,E,N)
    local p, q, a, AutN, OutN;

    
    Info(InfoFusion, 2, "\tChecking lift of type SL_2(q)");
    
    p := PrimePGroup(S);

    if p = 2 then return true; fi;

    q := Index(N, E);

    a := (q-1)/2;

    Info(InfoFusion, 2, "\tNeed an element of order ", a, " in Aut(N_S(E))");
    Info(InfoFusion, 2, "\tConstructing Aut(N_S(E))");
    # check Aut(N) has an element of order a
    AutN := AutomorphismGroupPGroup(N);
    if AutN.size mod a <> 0 then 
        Info(InfoFusion, 2, "\tNo element of order ", a, " in Aut(N_S(E))");
        return false;
    fi;
    if AutN.glOrder = 1 then 
        Info(InfoFusion, 2, "\tAut(N_S(E)) is solvable");
        AutN := PcGroupAutPGroup(AutN);
        OutN := AutN/PCore(AutN,p);
        Info(InfoFusion, 2, "\tp'-part : ", StructureDescription(OutN));
        if Exponent(OutN) mod a <> 0 or ForAll(ConjugacyClasses(OutN), x -> Order(Representative(x)) <> a) then
            Info(InfoFusion, 2, "\tNo element of order ", a, " in Aut(N_S(E))");
            return false;
        fi;
    fi;

    return true;
end;

# Lifts in $\Alt(2p)$ (p^2 only)
IsProtoEssentialSubgroup_EABLiftAlt := function(S,E,N)
    local p, AutN, OutN;

    p := PrimePGroup(S);
    
    Info(InfoFusion, 2, "\tChecking lift of type Alt(2p)");
    if p <= 3 then 
        Info(InfoFusion, 2, "\tDoesn't apply for p <= 3");
        return false;
    elif Index(N, E) <> p^2 then 
        Info(InfoFusion, 2, "\tDoesn't apply since Out_S(E) not eab order p^2");
        return false;
    fi;
    
    Info(InfoFusion, 2, "\tNeed a non-abelian subgroup of order ", (p-1), "^2", " in Aut(N_S(E))");
    Info(InfoFusion, 2, "\tConstructing Aut(N_S(E))");
    AutN := AutomorphismGroupPGroup(N);
    if AutN.size mod (p-1)^2 <> 0 then 
        Info(InfoFusion, 2, "\tNo subgroup of order ", (p-1), "^2", " in Aut(N_S(E))");
        return false;
    fi;
    if AutN.glOrder = 1 then 
        Info(InfoFusion, 2, "\tAut(N_S(E)) is solvable");
        AutN := PcGroupAutPGroup(AutN);
        OutN := AutN/PCore(AutN,p);
        Info(InfoFusion, 2, "\tp'-part : ", StructureDescription(OutN));
        if IsAbelian(OutN) then
            Info(InfoFusion, 2, "\tAny subgroup of order ", (p-1), "^2 is abelian in Aut(N_S(E))");
            return false;
        fi;
    fi;

    return true;
end;

InstallMethod(PE_LiftTest, "proto-essential lift test", [IsPGroup, IsPGroup, IsInt], function(S, E, i)
    local N;

    # cyclic/quaternion case - nothing guaranteed to lift
    # TODO: If a $p$-group has rank $< p$, then the cyclic Sylow can only lie inside
    # \SL_2(p) OR \PSL_2(p), i.e. $1/2(p-1)$ needs to lift here as well [only valid for $p \geq 3$, interesting for $p \geq 5$]
    if i = 0 then 
        return true;
    fi;

    N := Normalizer(S, E);
    
    Info(InfoFusion, 1, "Lift check for type ", i, " and order ", Index(N, E), 
        " with [Rank(N_S(E)), Class(N_S(E))] = ", [Rank(N), NilpotencyClassOfGroup(N)]);

    # eab case
    if i = 1 then
        if IsProtoEssentialSubgroup_EABLiftSL2q(S,E,N) or IsProtoEssentialSubgroup_EABLiftAlt(S,E,N) then 
            Info(InfoFusion, 1, "Lift check passed");
            return true;
        else 
            Info(InfoFusion, 1, "Lift check failed");
            return false;
        fi;
    fi;

    # TODO: Code others
    return true;
end );

# Checks, based on the order of the automorphism group, whether $\Aut(E)$ can have a valid section (for the given $i$)
# that is a valid simple group with a strongly $p$-embedded subgroup
IsAutSizeValid := function(S, E, i, AutE_order)
    local p, OutSE_order, n, r;

    p := PrimePGroup(S);

    OutSE_order := Index(Normalizer(S,E), E);
    n := PValuation(OutSE_order, p);
    r := Rank(E);

    if i=0 then 
        if p = 2 then 
            return true;
        # no group of order q or 2q has a strongly p-embedded subgroup
        elif IsPrimePowerInt(AutE_order) or (AutE_order mod 2 = 0 and IsPrimePowerInt(AutE_order/2)) then 
            return false;
        # the only group of order 4q that has a strongly p-embedded subgroup is Alt(4) at p=3
        elif p >= 5 and AutE_order mod 4 = 0 and IsPrimePowerInt(AutE_order/4) then
            return false;
        fi;
    fi;
    # eab case
    if (i=0 and n=1) or i=1 then 
        if AutE_order mod Size(PSL(2, p^n)) = 0 then 
            return true;
        # TODO: Also check for rank
        # Alt(2p)
        elif p >= 5 and AutE_order mod Factorial(2*p)/2 = 0 then 
            return true;
        elif p = 3 then 
            # TODO: Also check for rank
            # M11, PSL(3,4)
            return ForAny([7920, 20160], a -> AutE_order mod a = 0);
        elif p = 5 then 
            # ^2F_4(2)' and Fi_22
        fi;
        return false;
    # PSU(3,p^n)
    elif i=2 then 
        return AutE_order mod Size(PSU(3,p^(n/3))) = 0;
    fi;

    return false;
end;

IsProtoEssentialSubgroup_Aut_sol := function(S, E, i, AutE)
    local   p, # the prime
            AutSE, # Aut_S(E)
            InnE, # pc-representation of Inn(E)x
            AutE_PC, # pc-representation of Aut(E)
            AutEp, # O_p(AutE_PC)
            AutSE_PC, # pc-representation of Aut_S(E)
            n; # nice monomorphism for Aut(E)
    
    Info(InfoFusion, 2, "\tAut(E) is solvable");
    
    if i > 0 then 
        Info(InfoFusion, 1, "Invalid - Out_S(E) not cyclic/quaternion");
        return false;
    fi;

    # check that the size of the automorphism group is valid
    if not IsAutSizeValid(S, E, i, AutE.size) then 
        Info(InfoFusion, 1, "Invalid size of aut group");
        return false;
    fi;

    p := PrimePGroup(S);
    AutE_PC := PcGroupAutPGroup(AutE);
    AutSE := Automizer(S,E);
    AutEp := PCore(AutE_PC, p);

    AutE := ConvertHybridAutGroup(AutE);
    SetAutomorphismGroup(E, AutE);
    SetIsGroupOfAutomorphisms(AutE, true);
    SetAutomorphismDomain(AutE, E);

    n := GroupHomomorphismByImagesNC(AutE, AutE_PC);
    SetNiceMonomorphism(AutE, n);
    SetNiceObject(AutE, AutE_PC);
    
    if IndexNC(AutE_PC, AutEp) mod Index(Normalizer(S,E), E) <> 0 then 
        Info(InfoFusion, 1, "Out_S(E) cannot project onto Aut(E)/O_p(Aut(E))");
        return false;
    fi;
    
    Info(InfoFusion, 2, "\tOut_S(E) can project onto Aut(E)/O_p(Aut(E))");
    AutSE_PC := PcSubAutPGroup(AutE_PC, AutSE);

    # Aut_S(E) \cap O_p(\Aut(E)) = Inn(E)
    if Size(Intersection(AutSE_PC, AutEp)) <> Index(E, Center(E)) then 
        Info(InfoFusion, 1, "Not quasi-radical");
        return false;
    fi;
    
    Info(InfoFusion, 1, "Is quasi-radical");

    return true;
end;

IsProtoEssentialSubgroup_Aut_nsol := function(S, E, i, AutE)
    local   p, # the prime
            AutSE, # Aut_S(E)
            InnE, # Inn(E)
            AutEp, # O_p(AutE)
            G, # group generated by AutE/sol(AutE)
            C, # composition factors of G
            n; # nice nonomorphism for Aut(E)

    Info(InfoFusion, 2, "\tAut(E) is not solvable");

    if i > 0 then 
        G := Group(AutE.glOper);
        C := CompositionSeries(G);

        if ForAll([1..Length(C)-1], j -> not IsAutSizeValid(S, E, i, IndexNC(C[j], C[j+1]))) then 
            Info(InfoFusion, 1, "No valid composition factor with the right size");
            return false;
        fi;
    fi;

    p := PrimePGroup(S);
    AutSE := Automizer(S,E);

    AutE := ConvertHybridAutGroup(AutE);
    if not IsAbelian(E) then 
        InnE := InnerAutomorphismGroup(E);
    else
        InnE := TrivialSubgroup(AutE);
    fi; 

    SetAutomorphismGroup(E, AutE);
    SetIsGroupOfAutomorphisms(AutE, true);
    SetAutomorphismDomain(AutE, E);

    Info(InfoFusion, 2, "\tFinding nice monomorphism for Aut(E)");
    AssignNiceMonomorphismAutomorphismGroup(AutE, E);
    Info(InfoFusion, 2, "\tComputed");
    n := NiceMonomorphism(AutE);
    
    AutSE := Image(n, AutSE);
    AutE := Image(n, AutE);
    AutEp := PCore(AutE, p);
    InnE := Image(n, InnE);
    
    # Aut_S(E) \cap O_p(\Aut(E)) = Inn(E)
    if Size(Intersection(AutSE, AutEp)) <> IndexNC(E, Center(E)) then 
        Info(InfoFusion, 1, "Not quasi-radical");
        return false;
    fi;
    Info(InfoFusion, 1, "Is quasi-radical");
    
    return true;
end;

InstallMethod(PE_RadicalTest, "proto-essential radical test", [IsPGroup, IsPGroup, IsInt], function(S, E, i)
    local AutE;

    Info(InfoFusion, 1, "Constructing Aut(E) with OutSE of type ", i, " and order ", Index(Normalizer(S,E), E), 
        " with [Rank(E), Class(E)] = ", [Rank(E), NilpotencyClassOfGroup(E)]);

    # TODO: Bring more of sol/nsol together.
    # TODO: Optimise for the case when Aut(E) is already found.
    
    AutE := AutomorphismGroupPGroup(E, "Over");
    Info(InfoFusion, 2, "\tAut(E) has order ", AutE.size);

    if IsPrimePowerInt(AutE.size) then 
        Info(InfoFusion, 1, "Invalid -- Aut(E) is a p-group");
        return false;
    fi;

    if AutE.glOrder = 1 then 
        return IsProtoEssentialSubgroup_Aut_sol(S, E, i, AutE);
    else 
        return IsProtoEssentialSubgroup_Aut_nsol(S, E, i, AutE);
    fi;
end);

InstallMethod(PE_InvolutionsConjugate, "proto-essential involutions check", [IsPGroup, IsPGroup, IsInt], function(S, E, i)
    local p, AutE, AutSE, InnE, n, q, OutE, OutSE, N, C;

    p := PrimePGroup(S);

    if p <> 2 or i = 0 then 
        return true;
    fi;

    Info(InfoFusion, 1, "Involution conjugate check");

    AutE := AutomorphismGroup(E);
    AutSE := Automizer(S, E);
    if not IsAbelian(E) then 
        InnE := InnerAutomorphismGroup(E);
    else
        InnE := TrivialSubgroup(AutE);
    fi; 

    n := NiceMonomorphism(AutE);
    AutE := NiceObject(AutE);
    if IsBound(AutE!.autrec) then 
        AutSE := PcSubAutPGroup(AutE, AutSE);
        InnE := PcSubAutPGroup(AutE, InnE);
    else 
        AutSE := Image(n, AutSE);
        InnE := Image(n, InnE);
    fi;

    # check all the involutions in Out_S(E) are conjugate in N_{\Out(E)}(\Out_S(E))
    q := NaturalHomomorphismByNormalSubgroup(AutE, InnE);
    OutE := Image(q, AutE);
    OutSE := Image(q, AutSE);
    N := Normalizer(OutE, OutSE);

    C := ClassesSolvableGroup(OutSE, 0);
    C := List(C, x -> x.representative);
    C := Filtered(C, x -> Order(x) = 2);

    if ForAll(C, x -> IsConjugate(N, x, C[1])) then 
        Info(InfoFusion, 1, "Check passed");
        return true;
    else 
        Info(InfoFusion, 1, "Check failed");
        return false;
    fi;
end );

InstallMethod(IsProtoEssentialSubgroup, [IsPGroup, IsPGroup], function(S, E)
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

InstallMethod(PE_ValidAutomizers, "method for finding valid automizers", [IsPGroup, IsPGroup], function(S, E)
    local   AutE, # Aut(E)
            InnE, # Inn(E)
            AutSE, # Aut_S(E)
            p, # the prime
            n, # the nice monomorphism for Aut(E)
            L, # possible choices for Aut_F(E)
            i, # current position in L
            AutFE, # possible Aut_F(E)
            A, # O_p(Aut_F(E))
            q, # quotient map Aut_F(E) -> Aut_F(E)/A
            OutFE, # quotient Aut_F(E)/A
            OutSE, # quotient Aut_S(E)/A
            OutE, # quotient Aut(E)/A
            M, # the maximal subgroups of OutFE
            C, # the conjugates of subgroups in M containing OutSE
            I, # positions of conjugates in C containing OutSE
            a, # counter of new automizers
            X; # a subgroup in C

    Info(InfoFusion, 2, "Finding valid automizer(s)");

    p := PrimePGroup(S);

    AutE := AutomorphismGroup(E);
    n := NiceMonomorphism(AutE);
    InnE := Automizer(E, E);
    AutSE := Automizer(S, E);
    AutE := NiceObject(AutE);

    if IsBound(AutE!.autrec) then 
        InnE := PcSubAutPGroup(AutE, InnE);
        AutSE := PcSubAutPGroup(AutE, AutSE);
    else 
        InnE := Image(n, InnE);
        AutSE := Image(n, AutSE);
    fi;

    Info(InfoFusion, 2, "Finding valid automizer(s)");

    # Find subgroups containing AutSE within overgroups above p-core. Iterated maximal approach
    L := [PrimeResidual(AutE,p)];
    i := 0;

    while i < Length(L) do 
        i := i+1;
        AutFE := L[i];
        A := PCore(AutFE,p);

        q := NaturalHomomorphismByNormalSubgroup(AutFE, A);
        
        OutFE := Image(q);
        OutSE := Image(q, AutSE);
        Info(InfoFusion, 3, "\tFound section of order ", Size(OutFE));
        
        M := MaximalSubgroupClassReps(OutFE);
        Info(InfoFusion, 3, "\t\twhich has ", Length(M), " maximal subgroups");
        M := List(M, A -> PrimeResidual(A,p));
        C := List(M, A -> ContainedConjugates(OutFE, A, OutSE, true));
        I := PositionsProperty(C, A -> A <> fail);
        Info(InfoFusion, 3, "\t\tof which ", Length(I), " contain Aut_S(E)");

        C := List(I, i -> M[i]^(C[i][2]^-1));
        C := List(C, A -> PreImage(q, A));

        a := 0;
        # Add missing G-conjugates
        for X in C do 
            if Intersection(PCore(X,p), AutSE) = InnE and ForAll(L, T -> not IsConjugate(AutE, T, X)) then 
                a := a+1;
                Add(L, X);
            fi;
        od;
        Info(InfoFusion, 3, "\t\tTotal ", a, " new automizer(s) up to Aut(E)-conjugacy");
    od;

    q := NaturalHomomorphismByNormalSubgroup(AutE, InnE);
    OutE := Image(q);
    L := Filtered(L, A -> IndexNC(A, ClosureGroup(AutSE, PCore(A,p))) mod p <> 0);
    L := List(L, A -> Image(q, A));
    OutSE := Image(q, AutSE);

    Info(InfoFusion, 3, "\t", Length(L), " possible valid radical automizer(s) (mod p-core)");

    # TODO: Filter the elements in L that have a strongly p-embedded subgroup (mod p-core)
    Info(InfoFusion, 3, "\t", Length(L), " possible valid essential automizer(s) (mod p-core)");

    L := List(L, A -> ComplementClassesRepresentatives(A, PCore(A,p)));
    L := Flat(L);

    C := List(L, A -> RepresentativeAction(OutE, SylowSubgroup(A,p), OutSE));
    I := PositionsProperty(C, A -> A <> fail);
    L := List(I, i -> L[i]^C[i]);
    L := List(L, A -> PreImage(q, A));
    Info(InfoFusion, 2, Length(L), " valid essential automizer(s)");

    return List(L, A -> PreImage(n, A));
end );

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

    Info(InfoFusion, 1, "Constructing the holomorph of S");
    G := Holomorph(S);
    Info(InfoFusion, 1, "Constructed");
    i := Embedding(G, 2);
    S0 := Image(i, S);

    if not onlyOne then 
        L := LowerCentralSeries(S0);
        L := CompositionSeriesThrough(S0, L);
        
        # Deals with a bug in CompositionSeriesThrough
        j := Position(L, TrivialSubgroup(S0));
        L := L{[1..j]};
        
        j := Position(L, DerivedSubgroup(S0));
        L := L{[j+1..Length(L)]};
        Info(InfoFusion, 1, Length(L), " iterations");
        
        q := List(L, A -> NaturalHomomorphismByNormalSubgroup(S0,A));

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

        C := ClassesSolvableGroup(S0, 0);
        C := Filtered(C, a -> Order(a.representative) = p);
        C := List(C, a -> a.centralizer);
    fi;

    Info(InfoFusion, 1, Length(C), " subgroups, including possibly duplicates");
    Info(InfoFusion, 2, "\tFinding Aut(S) reps");

    C := Orbits(G, C);
    Info(InfoFusion, 1, Length(C), " up to Aut(S)-conjugacy");

    C := List(C, Representative);
    C := List(C, A -> PreImage(i, A));
    
    Info(InfoFusion, 1, "Checking proto-essentials");
    C := Filtered(C, E -> IsProtoEssentialSubgroup(S,E));

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
        
    G := Holomorph(S);
    i := Embedding(G, 2);
    S0 := Image(i, S);

    I := [];
    L0 := List(L, A -> Image(i, A));
    T := [];

    while Length(I) <> Length(L0) do 
        # we're dealing with some subgroup of largest order not yet considered
        J := Difference([1..Length(L0)], I);
        j := PositionMaximum(List(L0{J}, Size));
        j := J[j];
        E := L0[j];
        Add(I, j);
        Info(InfoFusion, 2, "Looking at position ", j);

        A0 := [E]; 
        A := List(T, X -> ContainedConjugates(G, X, E, true));
        A := Filtered(A, X -> X <> fail);
        Info(InfoFusion, 3, "\t", Length(A), " valid conjugate(s) of overgroup essentials");

        for F in A do
            E0 := E^(F[2]);

            AutF := AutomorphismGroup(F[1]);
            n := NiceMonomorphism(AutF);
            AutF := NiceObject(AutF);
            
            # Find Aut(F)-conjugates of subgroups in A0 that are not already present (up to Aut(S)-conjugacy)
            Info(InfoFusion, 3, "\t", "Finding Aut(F)-orbit of E");
            A0F := Orbit(AutF, E0, OnImageNM(n));
            Info(InfoFusion, 3, "\t", "Found");
            Info(InfoFusion, 3, "\t", "Orbit to Aut(S)-conjugacy");
            A0F := Orbits(G, A0F);
            Info(InfoFusion, 3, "\t", "Found");
            A0F := Filtered(A0F, X -> ForAll(A0, Y -> not Y in X));
            A0F := List(A0F, Representative);
            Append(A0, A0F);
            Info(InfoFusion, 3, "\t", Length(A0F), " new subs");
        od;

        A0 := Filtered(A0, X -> ForAll(L0, Y -> not IsConjugate(G, X, Y)));
        Append(L0, A0);

        if E in L0 or IsProtoEssentialSubgroup(S0, E) then 
            Info(InfoFusion, 2, "\t", "E is essential");
            Add(T, E);
        fi;
    od;
    T := List(T, A -> PreImage(i, A));

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
