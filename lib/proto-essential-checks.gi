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

InstallMethod(RankTest, "PE rank test", 
    [IsPGroup, IsPGroup], function(S, E)
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

    # p-rank 1
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

    # TODO: These are not currently determined up to isomorphism
    
    # PSU(3,p^n) [p odd]
    if p >= 3 and n mod 3 = 0 and Exponent(OutSE) = p and 
        Length(Set([Center(OutSE), DerivedSubgroup(OutSE), FrattiniSubgroup(OutSE)])) = 1 and 
        NilpotencyClassOfGroup(OutSE) = 2 and IsElementaryAbelian(Center(OutSE)) and 
        Size(Center(OutSE)) = p^(2*n/3) and HasElementaryAbelianFactorGroup(OutSE, Center(OutSE)) then 
        if r >= 6*n then 
            return 2;
        else 
            return -1;
        fi;
    fi;

    if p = 2 and 2*PValuation(Size(OutSE),2) <= r
        and Length(Set([Omega(OutSE, p), Center(OutSE), FrattiniSubgroup(OutSE), DerivedSubgroup(OutSE)])) = 1 then 
        # Sz(2^2n+1)
        if Size(OutSE) = Size(Omega(OutSE, p))^2 then 
            return 3;
        # PSU(3, 2^2n)
        elif Size(OutSE) = Size(Omega(OutSE, p))^3 then 
            return 2;
        fi;
    fi;

    # ^2 G_2(q)
    if p = 3 and 2*PValuation(Size(OutSE),p) <= r
        and Length(Set([Omega(OutSE, p), FS_SecondCentre(OutSE), FrattiniSubgroup(OutSE), DerivedSubgroup(OutSE)])) = 1 then 
        return 4;
    fi;
    
    # 3^{1+2}_-
    if Size(OutSE) = 3^3 and IdGroup(OutSE)[2] = 4 and r >= 6 then 
        return 5;
    # 5^{1+2}_-
    elif Size(OutSE) = 5^3 and IdGroup(OutSE)[2] = 4 and r >= 20 then 
        return 5;
    fi;

    return -1;
end );

InstallMethod(ModuleTest, "PE Module Test", 
    [IsPGroup, IsPGroup], function(S, P)
    local p,FP,NSP,k,l,s,sP;

    p := PrimePGroup(S);
    if p <> 2 then return true; fi;

    FP := FrattiniSubgroup(P);
    NSP := Normalizer(S,P); 

    k := PValuation(IndexNC(NSP, P), p);
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
end );

InstallMethod(FrattiniTest, "PE Frattini Test", 
    [IsPGroup, IsPGroup], function(S, E)
    # Specific case when $C_{N_S(E)}(E/\Phi(E)) = N_S(E)$
    if CommutatorSubgroup(Normalizer(S,E), E) = FrattiniSubgroup(E) then 
        return false;
    fi;

    return CentralizerMod(Normalizer(S,E),E,FrattiniSubgroup(E)) = E;
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

    # TODO: This lift is an abelian group, so we can check up to isomorphism as well.
    
    # cyclic/quaternion case - nothing guaranteed to lift
    # TODO: If the rank of $E$ is small enough, the $C_p$ might be a subgroup of $\PSL_2(p)$
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
        return CheckLift((p^2-1)/Gcd(3,p-1), (p^2-1)/Gcd(3,p-1));
    elif i = 3 then 
        return CheckLift(p^(n/3)-1, p^(n/3)-1);
    elif i = 4 then 
        return CheckLift(p^n-1, p^n-1);
    elif i = 5 then 
        return CheckLift(p-1, p-1);
    else
        Error("Invalid value i");
    fi;
end );

InstallMethod(ValidAutTest, "PE Valid Aut Test",
    [IsPGroup, IsPGroup, IsInt], function(S, E, i)
    local OutSE, p, n, r, q, AutE, N, AutEp, D, IsSectionOrderValid;

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
            if a mod (r*(r-1)*(r+1)) = 0 then 
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
            # elif n=3 and p=5 and a mod ... = 0 then
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
    local i;
    if not FrattiniTest(S, E) then 
        Info(InfoFusion, 2, "\tFailed frattini test");
        return false;
    fi;

    if not ModuleTest(S, E) then
        Info(InfoFusion, 2, "\tFailed module test");
        return false;
    fi;

    i := RankTest(S, E);
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
    if S = E or not IsSubset(E, Centralizer(S,E)) then 
        Info(InfoFusion, 2, "\tFailed centric test");
        return false;
    fi;

    if not Zed0Test(S, E) then 
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
