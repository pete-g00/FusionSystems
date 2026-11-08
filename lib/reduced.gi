# If $P$ has class $\leq n(p-1)+1$, then $Z(P)$ has exponent $\leq p^n$
InstallMethod(ExponentTest, "RED exponent test",
    [IsPGroup], function(S)
    local c, t, p;
    
    if IsAbelian(S) then return false; fi;
    p := PrimePGroup(S);
    
    c := NilpotencyClassOfGroup(S);
    t := Int(Ceil(Float((c-1)/(p-1))));

    return Exponent(Center(S)) <= p^t;
end );

InstallMethod(SemiCharacteristicGeneratedTest, "RED semi-characteristic generated test", 
    [IsPGroup, IsList], function(S, L)
    local p, AutS, n, C, E, A, QE;

    if IsAbelian(S) then return false; fi;
    
    # Compute [O^p(Aut(S)), S]
    p := PrimePGroup(S);
    
    AutS := AutomorphismGroup(S);
    n := NiceMonomorphism(AutS);
    AutS := n(AutS);
    AutS := PResidual(AutS, p);
    AutS := PreImage(n, AutS);

    C := CommutatorSubgroup(AutS, S);
    
    if C = S then return true; fi;

    for E in L do 
        A := CommutatorSubgroup(Normalizer(S,E), E);
        QE := SemiCharacteristicClosure(E, A);
        # take normal closure to consider every S-conj. of E
        C := ClosureGroup(C, NormalClosure(S, QE));
        if C = S then return true; fi;
    od;

    return false;
end );

InstallMethod(TransferTest, "RED transfer test",
    [IsPGroup, IsList], function(S, L)
    local AutS, K, KF;
    
    if IsAbelian(S) then return false; fi;

    AutS := AutomorphismGroup(S);
    if not IsPGroup(AutS) then return true; fi;

    K := List(L, A -> Kernel(TransferHomomorphism(S, A)));
    return Intersection(K) = DerivedSubgroup(S);
end );

InstallMethod(TransferMaximalTest, "RED transfer maximal test",
    [IsPGroup], function(S)
    return TransferTest(S, MaximalSubgroups(S));
end );

InstallMethod(TransferFpTest, "RED transfer fp test",
    [IsPGroup, IsList], function(S, L)
    local AutS, K, KF;
    
    if IsAbelian(S) then return false; fi;

    AutS := AutomorphismGroup(S);
    if not IsPGroup(AutS) then return true; fi;

    K := List(L, A -> Kernel(TransferHomomorphismFp(S, A)));
    return Intersection(K) = FrattiniSubgroup(S);
end );

InstallMethod(TransferFpMaximalTest, "RED transfer fp maximal test",
    [IsPGroup], function(S)
    return TransferFpTest(S, MaximalSubgroups(S));
end );

InstallMethod(CoreTest, "RED core test",
    [IsPGroup, IsList], function(S, L)
    local N;
    
    if IsAbelian(S) then return false; fi;

    N := NormalSubgroups(S);
    return ForAll(N, A -> IsTrivial(A) or
        not ForAll(L, E -> IsSubset(E, A) and IsSemiCharacteristic(E, A))
    );
end );

InstallMethod(IsDSWGroup, "is DSw group",
    [IsPGroup], function(S)
    local p, n, M, a;

    if IsAbelian(S) then return false; fi;

    p := PrimePGroup(S);
    if p <> 2 then 
        a := Number(MaximalSubgroups(S), IsAbelian); 
        if a = 0 then 
            return false;
        elif a = 1 then 
            return true;
        else 
            return Size(S) = p^3 and Exponent(S) = p;
        fi;
    fi;

    n := PValuation(Size(S), p);

    # Dihedral/semidihedral case
    if NilpotencyClassOfGroup(S) = n-1 then 
        return Size(Omega(S, p)) <> p;
    fi;

    # $C_{2^a} \wr C_2$ only
    if IsEvenInt(n) then return false; fi;

    a := (n-1)/2;

    if NilpotencyClassOfGroup(S) <> a+1 then return false; fi;

    M := MaximalSubgroups(S);
    return ForAny(M, A -> IsAbelian(A) and Rank(A) = 2 and Length(Set(AbelianInvariants(A))) = 1);
end );

InstallMethod(AbelianTest, "RED abelian test",
    [IsPGroup], function(S)
    local p, C0, M;

    if IsAbelian(S) then return false; fi;
    
    p := PrimePGroup(S);
    if p <> 2 then return true; fi;

    if IsDSWGroup(S) then return true; fi;

    if NilpotencyClassOfGroup(S) = 2 then 
        M := MaximalSubgroups(S);
    else 
        M := [Centralizer(S, FS_SecondCentre(S))];
    fi;
    
    if ForAny(M, A -> IsAbelian(A) and Index(S, A) = 2) then 
        return false; 
    fi;

    C0 := ClassesSolvableGroup(S, 0);
    C0 := List(C0, x -> x.centralizer);
    C0 := Filtered(C0, A -> IsAbelian(A) and Index(Normalizer(S,A), A) = 2);

    return ForAll(C0, A -> not IsElementaryAbelian(A));
end );

InstallMethod(DerivedCyclicTest, "RED derived cyclic test",
    [IsPGroup], function(S)
    return IsDSWGroup(S) or not IsCyclic(DerivedSubgroup(S));
end );

InstallMethod(ValidAutTest, "RED valid aut test",
    [IsPGroup], function(S)
    local p, AutS, n, H;

    if IsAbelian(S) then return false; fi;

    p := PrimePGroup(S);
    if p = 2 then return true; fi;
    
    AutS := AutomorphismGroup(S);

    if p >= 5 and IsPGroup(AutS) then 
        return false;
    elif p = 3 and IsPGroup(AutS) and NilpotencyClassOfGroup(S) = 2 then 
        return false;
    elif NilpotencyClassOfGroup(S) > p or 
        (NilpotencyClassOfGroup(S) = p and (Size(S) > p^(p+1) or IsElementaryAbelian(Centralizer(S, FS_SecondCentre(S))))) then 
        return true;
    fi;

    n := NiceMonomorphism(AutS);
    AutS := n(AutS);
    if not IsNormal(AutS, SylowSubgroup(AutS, p)) then 
        return true;
    fi;

    H := SylowComplement(AutS, p);
    H := PreImage(n, H);

    return CommutatorSubgroup(H, S) = S;
end );

BindGlobal("FS_OmegaAbelianizationTest1", function(S)
    local p, AutS, O, D;

    if IsAbelian(S) then return false; fi;
    p := PrimePGroup(S);

    if p <> 2 then 
        return true; 
    fi;

    O := Omega(Center(S), p);
    D := DerivedSubgroup(S);

    return Index(O, Intersection(O, D)) <> 2;
end );

BindGlobal("FS_OmegaAbelianizationTest2", function(S)
    local p, AutS, O, D;

    if IsAbelian(S) then return false; fi;
    p := PrimePGroup(S);

    if p <> 2 then 
        return true; 
    fi;

    O := Omega(Center(S), p);
    D := DerivedSubgroup(S);

    AutS := AutomorphismGroup(S);

    return not IsPGroup(AutS) or IsSubset(D, O);
end );

InstallMethod(OmegaAbelianizationTest, "RED omega abelianization test",
    [IsPGroup], function(S)
    local p, AutS, O, D;

    return FS_OmegaAbelianizationTest1(S) or FS_OmegaAbelianizationTest2(S);
end );

InstallMethod(C0Test, "RED C0 test",
    [IsPGroup, IsList], function(S, C0)
    local p;
    
    if IsAbelian(S) then return false; fi;

    p := PrimePGroup(S);
    return not ForAll(C0, A -> IsSemiCharacteristic(A, Omega(Center(S), p)));
end );

InstallMethod(CTest, "RED C test",
    [IsPGroup, IsList], function(S, C)
    local p, AutS;
    
    if IsAbelian(S) then return false; fi;

    if IsEmpty(C) then 
        return false;
    elif Length(C) = 1 and IsNormal(S, C[1]) then 
        return false;
    elif Length(C) > 1 then
        return true;
    fi;
    # TODO: If p=2 and there is an abelian sub in C, then S must be DSW

    AutS := AutomorphismGroup(S);
    return not IsPGroup(AutS);
end );

# ONLY DEALS WITH INDECOMPOSABLE CASES
BindGlobal("FS_ReducedFusionSystems_Class2", function(S)
    local p, n;

    Assert(0, PClassPGroup(S) = 2 or NilpotencyClassOfGroup(S) = 2);
    
    p := PrimePGroup(S);
    n := PValuation(Size(S), p);
    
    # $\PSp_4(2^a)$ -> Syl-$2$ has order $2^{4a}$
    # $\L_3(p^a)$ OR $\Alt(6)$ ($p=2$) -> Syl-$p$ has order $p^{3a}$
    if IsOddInt(p) and n mod 3 <> 0 then 
        return false;
    elif p=2 and n mod 3 <> 0 and n mod 4 <> 0 then 
        return false;
    fi;
    
    # TODO: actually check whether these groups are valid
    return true;
end );

BindGlobal("FS_PossiblySupportsReducedFusionSystems_PrePE", function(S)
    if not ExponentTest(S) then 
        Info(InfoFusion, 1, "Exponent of Z(S) too big");
        return false;
    fi;

    # If $S'$ is cyclic, then $S$ must have an abelian index p 
    # TODO: Further check that that this sub proto-essential too
    if not DerivedCyclicTest(S) and not IsDSWGroup(S) then 
        Info(InfoFusion, 1, "Derived subgroup is cyclic");
        return false;
    fi;

    if not FS_OmegaAbelianizationTest1(S) then 
        Info(InfoFusion, 1, "Failed omega test (1)");
        return false;
    fi;

    if not AbelianTest(S) then 
        Info(InfoFusion, 1, "Failed abelian test");
        return false;
    fi;

    return true;
end);

InstallMethod(PossiblySupportsReducedFusionSystems_PE, "Possibly supports reduced fusion systems (PE version)",
    [IsPGroup, IsList], function(S, C)
    local p, L;
    
    if not FS_PossiblySupportsReducedFusionSystems_PrePE(S) then 
        return false;
    fi;

    p := PrimePGroup(S);
    
    if not CTest(S, C) then 
        Info(InfoFusion, 1, "Failed C test");
        return false;
    fi;

    if not TransferTest(S, C) or not TransferFpTest(S, C) then 
        Info(InfoFusion, 1, "Failed transfer test");
        return false;
    fi;

    L := GenerateProtoEssentials(S, C);

    if not ValidAutTest(S) then 
        Info(InfoFusion, 1, "Failed valid Aut(S) test");
        return false;
    fi;

    if not CoreTest(S, L) then 
        Info(InfoFusion, 1, "Failed core test");
        return false;
    fi;

    if not SemiCharacteristicGeneratedTest(S, L) then 
        Info(InfoFusion, 1, "Failed semi-characteristic generation test");
        return false;
    fi;

    return true;
end );

InstallMethod(PossiblySupportsReducedFusionSystems, "Possibly supports reduced fusion systems",
    [IsPGroup], function(S)
    local C0, C;
    
    # TODO: Maximal class
    # TODO: Abelian sub. of index p (non-maximal class)

    # TODO: Deal with p odd as well
    if PrimePGroup(S) = 2 and IsDSWGroup(S) then 
        Info(InfoFusion, 1, "S is DSW group");
        return true; 
    # elif (PClassPGroup(S) = 2 or NilpotencyClassOfGroup(S) = 2) then 
    #     if FS_ReducedFusionSystems_Class2(S) then 
    #         Info(InfoFusion, 1, "S is valid of class 2");
    #         return true;
    #     else 
    #         Info(InfoFusion, 1, "S is invalid of class 2");
    #         return false;
    #     fi;
    elif IsAbelian(S) then 
        Info(InfoFusion, 1, "S is abelian");
        return false; 
    fi;

    if not FS_PossiblySupportsReducedFusionSystems_PrePE(S) then 
        return false;
    fi;

    C0 := MainProtoEssentials(S, 0);
    if not C0Test(S, C0) then 
        Info(InfoFusion, 1, "Failed C0 test");
        return false;
    fi;

    if not FS_OmegaAbelianizationTest2(S) then 
        Info(InfoFusion, 1, "Failed C0 test");
        return false;
    fi;

    C := MainProtoEssentials(S, -1);
    C := Flat([C, C0]);

    return PossiblySupportsReducedFusionSystems_PE(S, C);
end );
