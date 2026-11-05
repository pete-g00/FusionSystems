BindGlobal("FS_SecondCentre", function(S)
    local q;
    q := NaturalHomomorphismByNormalSubgroupNC(S, Centre(S));
    return PreImage(q, Centre(Image(q)));
end);

InstallMethod(Zed0, "Computes Zed0 for a group", 
    [IsPGroup], function(S)
    local p, Z2S, ZS, T, Zp, t, A;

    p := PrimePGroup(S);
    Z2S := FS_SecondCentre(S);
    ZS := Centre(S);

    # Not sure whether computing a transversal is more efficient
    # overall or not but...
    T := RightTransversal(Z2S,ZS);

    # ... note [t, S] = [tz, S] for each z in Z(S), so we only need
    # check the commutator condition on a set of coset representatives
    # for Z(S) in Z_2(S).
    Zp := ZS;
    for t in T do
        A := Group(t);
        if Size(CommutatorSubgroup(S, A)) = p then 
            Zp := ClosureGroup(Zp, A);
            if Zp = Z2S then 
                break;
            fi;
        fi;
    od;

    return Zp;
end );

InstallMethod(Zed0Test, "PE Z0 test",
    [IsPGroup, IsPGroup], function(S, E)
    local Zed, p, OS, OE;

    Zed := Zed0(S);
    if IsSubset(E, Zed) then 
        return true;
    fi;

    p := PrimePGroup(S);

    if Index(Normalizer(S,E), E) <> p then 
        return false;
    fi;

    OS := Omega(Center(S),p);
    OE := Omega(Center(E),p);

    if not IsSubset(OE, OS) then 
        return false;
    fi;

    return ForAny(RightTransversal(OE, OS), x -> Centralizer(S, x) = E);
end );

# [SAM14, Theorem 6.9, Proposition 6.10]: if E is essential in a saturated fusion system and E/Phi(E) has rank r, then
# N = Out_S(E) is a Sylow p-subgroup of a group with a strongly p-embedded subgroup acting faithfully on E/Phi(E), so
# |N|^2 <= p^r and N is cyclic, quaternion, elementary abelian, or of one of the following types: for p = 2, a Suzuki
# 2-group with Omega(N) = Z(N) = Phi(N) = N' and |N| = |Z(N)|^2 or |Z(N)|^3 (Sz(2^n), PSU(3, 2^n)); for odd p, a group of
# exponent p with Z(N) = N' = Phi(N) elementary abelian of order |N|^(1/3) (PSU(3, p^n)); for p = 3, 5, the extraspecial
# group p^(1+2)_-; for p = 3, a group with |N| = |Z(N)|^3 = 3^(6n+3), n >= 1, and Omega(N) = Phi(N) = N' = Z_2(N)
# elementary abelian of order |Z(N)|^2 (Ree groups). The bound on |N| is [PS_MAGMA, Lemma 4.7, Proposition 4.8(4)] and
# the list of types is [PS_MAGMA, Corollary 4.6, Proposition 4.8(3)]. For p = 2, all of this follows from Bender's
# theorem; for odd p, it depends on the classification of finite simple groups.
InstallGlobalFunction(SPESylowType, function(S0, arg...)
    local p, Z, Om, Phi, Der;

    if IsTrivial(S0) then 
        return -1; 
    fi;

    p := PrimePGroup(S0);

    if not IsEmpty(arg) and Size(S0)^2 > p^arg[1] then
        return -1;
    elif IsCyclic(S0) then
        return 0;
    elif IsElementaryAbelian(S0) then
        return 1;
    fi;

    # a noncyclic p-group with a unique subgroup of order p is generalized quaternion
    Om := Omega(S0, p);
    if Size(Om) = p then
        return 0;
    fi;
    
    Z := Center(S0);
    Phi := FrattiniSubgroup(S0);
    Der := DerivedSubgroup(S0);
    
    if p = 2 and Om = Z and Phi = Z and Der = Z and Size(S0) = Size(Z)^2 then
        return 3;
    elif p = 2 and Om = Z and Phi = Z and Der = Z and Size(S0) = Size(Z)^3 then
        return 2;
    elif IsOddInt(p) and Exponent(S0) = p and IsElementaryAbelian(Z) and Der = Z and Phi = Z and Size(S0) = Size(Z)^3 then
        return 2;
    elif p in [3, 5] and Size(S0) = p^3 and Exponent(S0) = p^2 and not IsAbelian(S0) then
        return 5;
    elif p = 3 and Size(S0) > 27 and Size(S0) = Size(Z)^3 and PadicValuation(Size(S0), 3) mod 6 = 3 and
           Om = Phi and Om = Der and Om = FS_SecondCentre(S0) and IsElementaryAbelian(Om) and Size(Om) = Size(Z)^2 then 
        return 4;
    fi;

    return -1;
end );

InstallMethod(ModuleTest, "PE Module Test", 
    [IsPGroup, IsPGroup], function(S, E)
    local p, d, FP, N, hom, S0, dims, C, s, mDim, Z, n, k;
    
    p := PrimePGroup(S);
    if p <> 2 then return true; fi;
    if IsCyclic(E) or S = E then return false; fi;

    d := RankPGroup(E);
    FP := FrattiniSubgroup(E);

    N := Normalizer(S, E);
    hom := NaturalHomomorphismByNormalSubgroup(N, E);
    S0 := Image(hom);
    k := PValuation(Size(S0), 2);

    # dimensions of [s, E/Phi(E)] for representatives s of the nontrivial classes of S0
    dims := [];
    C := ConjugacyClasses(S0);
    for s in C do
        s := Representative(s);
        if s <> One(S0) then
            s := PreImagesRepresentative(hom, s);
            Add(dims, PValuation(Size(ClosureGroup(FP, List(GeneratorsOfGroup(E), x -> Comm(x, s)))), 2) - PValuation(Size(FP), 2));
        fi;
    od;

    mDim := Minimum(dims);
    Z := Center(S0);

    n := PValuation(Size(Z), 2);
    if d < 2*k or (k >= 2 and mDim < 2) or (IsElementaryAbelian(Z) and mDim < n) or
        (k >= 3 and Size(Omega(S0, 2)) = 2 and (d < 3 * 2^(k - 2) or mDim < 2^(k - 2))) then
        Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails ModuleTest");
        return false;
    fi;

    return true;
end );

InstallMethod(FrattiniTest, "PE Frattini Test", 
    [IsPGroup, IsPGroup], function(S, E)
    local p, N, FP, Theta, T, C;

    p := PrimePGroup(S);
    
    if IsCyclic(E) or S = E then
        return false;
    fi;

    N := Normalizer(S, E);
    FP := FrattiniSubgroup(E);

    for Theta in [TrivialSubgroup(E), Center(E), FS_SecondCentre(E)] do
        T := ClosureGroup(FP, Theta);
        C := CentralizerMod(N, E, T);
        if Size(T) > Size(FP) then
            C := Intersection(C, CentralizerMod(N, T, FP));
        fi;
        if Size(C) > Size(E) then
            Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails FrattiniTest");
            return false;
        fi;
    od;

    return true;
end );

InstallMethod(LiftTest, "PE Lift Test", 
    [IsPGroup, IsPGroup, IsInt], function(S, E, i)
    local p, N, n, CheckLift;

    # TODO: Do a stronger check involving the structure of the group (e.g. if it is cyclic/abelian)
    # Check that a divides:
    # - $N_{\Aut(E)}(\Aut_S(E))$;
    # - $[N_{\Out(E)}(\Out_S(E)) : C_{\Out(E)}(\Out_S(E))]$; and
    # - $\Aut(N_S(E))$
    CheckLift := function(a, e)
        local N, AutN, AutSE, AutE, n, InnE, q, OutE, OutSE, C;
        
        N := Normalizer(S, E);
        AutN := AutomorphismGroup(N);

        if not (Size(AutN) mod a = 0 and Exponent(AutN) mod e = 0) then 
            return false;
        fi;

        AutSE := Automizer(S, E);
        AutE := AutomorphismGroup(E);
        n := NiceMonomorphism(AutE);

        AutSE := Image(n, AutSE);
        AutE := Image(n, AutE);

        N := Normalizer(AutE, AutSE);

        if not (Size(N) mod a = 0 and Exponent(N) mod e = 0) then
            return false;
        fi;

        # TODO: inner aut grp doesn't work when the gp. is abelian
        if not IsAbelian(E) then 
            InnE := InnerAutomorphismGroup(E);
            InnE := Image(n, InnE);
        else 
            InnE := TrivialSubgroup(AutE);
        fi;

        q := NaturalHomomorphismByNormalSubgroup(AutE, InnE);
        OutE := Image(q, AutE);
        OutSE := Image(q, AutSE);

        N := Normalizer(OutE, OutSE);
        C := Centralizer(OutE, OutSE);

        return IndexNC(N, C) mod a = 0;
    end;

    p := PrimePGroup(S);
    N := Normalizer(S,E);
    n := PValuation(Index(N, E), p);

    # cyclic/quaternion case - nothing guaranteed to lift
    # TODO: If the rank of $E$ is small enough, the $C_p$ might be a subgroup of $\PSL_2(p)$?
    if i = 0 then 
        return true;
    elif i = 1 then 
        if CheckLift((p^n-1)/Gcd(2, p-1), (p^n-1)/Gcd(2, p-1)) then 
            return true;
        else
            # TODO: the rank must also be sufficiently big here
            return n=2 and p>=5 and CheckLift((p-1)^2, 2*(p-1));
        fi;
    elif i = 2 then 
        return CheckLift((p^2-1)/Gcd(3,p+1), (p^2-1)/Gcd(3,p-1));
    elif i = 3 and n mod 2 = 0 then 
        return CheckLift(p^(n/2)-1, p^(n/2)-1);
    elif i = 4 and n mod 3 = 0 then 
        return CheckLift(p^(n/3)-1, p^n-1);
    elif i = 5 then 
        return CheckLift(p-1, p-1);
    elif i = -1 then 
        Info(InfoFusion, 3, "subgroup of order ", Size(E), " fails LiftTest");
        return false;
    else
        Error("Invalid value i");
    fi;
end );

InstallMethod(ValidAutTest, "PE Valid Aut Test",
    [IsPGroup, IsPGroup, IsInt], function(S, E, i)
    local OutSE, p, n, r, q, AutE, N, AutEp, D, IsSectionOrderValid;

    if i = -1 then return false; fi;

    OutSE := IndexNC(Normalizer(S,E), E);
    
    p := PrimePGroup(S);
    n := PValuation(OutSE, p);
    r := Rank(E);
    q := p^n;

    IsSectionOrderValid := function(a)
        local r;

        if IsPrimeInt(a) then return false; fi;

        # eab case
        if i=1 then 
            r := p^n;
            # PSL(2,r)
            if p = 2 and a mod (r^3 - r) = 0 then
                return true;
            elif IsOddInt(p) and 2*a mod (r^3 - r) = 0 then 
                return true;
            # Alt(2p)
            elif n=2 and p>=5 and 2*a mod Factorial(2*p) = 0 then 
                return true;
            # PSL(3,4)
            elif n=2 and p=3 and a mod 20160 = 0 then 
                return true;
            # M11
            elif n=2 and p=3 and a mod 7920 = 0 then 
                return true;
            # 2F42'
            elif n=2 and p=5 and a mod 17971200 = 0 then
                return true;
            # Fi22
            elif n=2 and p=5 and a mod 64561751654400 = 0 then
                return true;
            fi;
        elif i=2 then 
            r := p^(n/3);
            # PSU(3,r)
            if a mod (r^3*(r^3+1)*(r^2-1)/Gcd(3,r+1)) = 0 then 
                return true;
            # McL
            elif n=3 and p=5 and a mod 898128000 = 0 then 
                return true;
            # J2
            elif n=3 and p=5 and a mod 604800 = 0 then
                return true;
            fi;
        elif i=3 then 
            r := p^(n/2);
            # Sz(2^r)
            if a mod (r^2*(r^2+1)*(r-1)) = 0 then 
                return true;
            fi;
        elif i=4 then 
            r := p^(n/3);
            # ^2G_2(3^r)
            if a mod (r^3*(r^3+1)*(r-1)) = 0 then 
                return true;
            fi;
        elif i=5 then 
            # PSL(2,8)
            if p=3 and n=3 and a mod 504 = 0 then 
                return true;
            elif p=5 and n=3 and a mod 32537600 = 0 then 
                return true;
            fi;
        fi;

        return false;
    end;

    AutE := AutomorphismGroup(E);

    # If $\Aut(E)$ is solvable, cannot have $i = 0$
    if IsSolvable(AutE) and i <> 0 then 
        return false;
    fi;
    
    N := NiceMonomorphism(AutE);
    AutE := Image(N, AutE);

    # If $i=0$, check that $Aut(E)$ is not $p$-closed
    if i = 0 then 
        if not IsSolvable(AutE) then return true; fi;
        AutEp := SylowSubgroup(AutE, p);
        return not IsNormal(AutE, AutEp);
    fi;

    # If $i \neq 0$, $\Aut(E)$ is not solvable, and we can look at the composition factor sizes
    D := CompositionSeries(AutE);

    return ForAny([1..Length(D)-1], i -> IsSectionOrderValid(IndexNC(D[i], D[i+1])));
end );

InstallMethod(RadicalTest, "PE Radical Test", 
    [IsPGroup, IsPGroup], function(S, E)
    local p, AutE, AutSE, n, AutEp;

    p := PrimePGroup(S);

    AutE := AutomorphismGroup(E);
    AutSE := Automizer(S, E);
    n := NiceMonomorphism(AutE);

    AutE := Image(n, AutE);
    AutSE := Image(n, AutSE);

    AutEp := PCore(AutE, p);

    return Size(Intersection(AutEp, AutSE)) = IndexNC(E, Center(E));
end);

InstallMethod(IsProtoEssentialNC, "PE check NC",
    [IsPGroup, IsPGroup], function(S, E)
    local N, i;
    if not FrattiniTest(S, E) then 
        Info(InfoFusion, 2, "\tFailed frattini test");
        return false;
    fi;

    if not ModuleTest(S, E) then
        Info(InfoFusion, 2, "\tFailed module test");
        return false;
    fi;

    N := Normalizer(S, E);
    i := SPESylowType(N/E, Rank(E));
    if i=-1 then 
        Info(InfoFusion, 2, "\tFailed rank test");
        return false;
    fi;

    if not LiftTest(S, E, i) then 
        Info(InfoFusion, 2, "\tFailed lift test");
        return false;
    fi;

    if not ValidAutTest(S, E, i) then 
        Info(InfoFusion, 2, "\tFailed valid aut test");
        return false;
    fi;

    if RadicalTest(S, E) then 
        return true;
    else 
        Info(InfoFusion, 2, "\tFailed radical test");
        return false;
    fi;
end);

InstallMethod(IsProtoEssential, "PE check", 
    [IsPGroup, IsPGroup], function(S, E)
    if S = E then  
        Info(InfoFusion, 2, "\tE = S");
        return false;
    elif S = E or not IsSubset(E, Centralizer(S,E)) then 
        Info(InfoFusion, 2, "\tFailed centric test");
        return false;
    elif not Zed0Test(S, E) then 
        Info(InfoFusion, 2, "\tFailed Z0 test");
        return false;
    fi;

    return IsProtoEssentialNC(S, E);
end);

# FrattiniTest := function(S, P)
#     local ucs, FP, Theta, g;

#     ucs := Reversed(UpperCentralSeries(P));
#     FP := FrattiniSubgroup(P);
#     for Theta in ucs{[1..Minimum(2,Length(ucs))]} do 
#         for g in RightTransversal(Normalizer(S,P),P) do
#             if g in P then 
#                 continue; 
#             fi;
#             if IsSubgroup(ClosureGroup(Theta,FP), CommutatorSubgroup(Group(g),P))
#                     and IsSubgroup(FP, CommutatorSubgroup(Group(g), Theta)) then
#                 return false;
#             fi;
#         od;   
#     od;
#     return true;
# end;
