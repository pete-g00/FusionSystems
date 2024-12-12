InstallMethod(IsomType, "generic method",
    [IsGroup],
    function(A)
        if IdGroupsAvailable(Size(A)) then 
            return IdGroup(A);
        fi;

        return [
            Size(A),
            Exponent(A),
            List(LowerCentralSeries(A), Size),
            List(UpperCentralSeries(A), Size),
            List(DerivedSeries(A), Size),
            Size(FrattiniSubgroup(A)),
        ];
    end );

InstallGlobalFunction(OnImage, function(x, phi)
    return Image(phi, x);
end );

InstallGlobalFunction(OnImageTuples, function(L, phi)
    return List(L, x -> Image(phi, x));
end );

InstallGlobalFunction(OnHomConjugation, function(phi, psi)
    local A, B, B0, A0, psi1, psiA, psiB;

    Assert(0, IsGroupHomomorphism(phi) and IsGroupHomomorphism(psi));

    A := Source(phi);
    B := Image(phi);

    Assert(0, IsSubset(Source(psi), A));
    Assert(0, IsSubset(Source(psi), B));

    B0 := Image(psi, B);
    A0 := Image(psi, A);
    Assert(0, IsGroup(A0) and IsGroup(B0));

    psiA := RestrictedHomomorphism(psi, B, B0);
    psi1 := RestrictedInverseGeneralMapping(psi);
    Assert(0, IsGroupHomomorphism(psi1));
    psiB := RestrictedHomomorphism(psi1, A0, A);

    return psiB * phi * psiA;
end );

InstallGlobalFunction(OnHomListConjugation, function(L, psi)
    return List(L, phi -> OnHomConjugation(phi, psi));
end );

InstallGlobalFunction(OnAutGroupConjugation, function(A, psi)
    local B;

    Assert(0, IsGroupOfAutomorphisms(A));
    Assert(0, IsGroupHomomorphism(psi));
    Assert(0, IsSubset(Source(psi), Source(Representative(A))));

    if IsTrivial(A) then 
        return Group(IdentityMapping(Image(psi, Source(Representative(A)))));
    fi;

    B := Group(OnHomListConjugation(GeneratorsOfGroup(A), psi));
    if IsInjective(psi) then 
        SetSize(B, Size(A));
    fi;

    return B;
end );

InstallGlobalFunction(OnCoCl, function(P)
    return function(x, phi)
        return Image(phi, Representative(x))^P;
    end;
end );

InstallGlobalFunction(OnCoCle, function(P)
    return function(x, a)
        return (Representative(x)^a)^P;
    end;
end );

InstallMethod(RestrictedHomomorphism, "generic method",
    [IsGroupHomomorphism, IsGroup, IsGroup],
    function(phi, A, B)
        local P, Q;

        P := Source(phi);
        if not IsSubset(P, A) then 
            Error("A is not a subgroup of the domain.");
        fi;

        Q := Image(phi, A);
        if not IsSubset(B, Q) then 
            Error("The codomain is not a subgroup of B.");
        fi;

        return RestrictedHomomorphismNC(phi, A, B);
    end);

InstallMethod(RestrictedHomomorphismNC, "generic method",
    [IsGroupHomomorphism, IsGroup, IsGroup],
    function(phi, A, B)
        local AGens, ImageAGens;
    
        AGens := GeneratorsOfGroup(A);
        ImageAGens := List(AGens, a -> Image(phi, a));
        return GroupHomomorphismByImagesNC(A, B, AGens, ImageAGens);
    end);

InstallMethod(FindPrimeOfPrimePower, "generic method",
    [IsScalar],
    function(q)
        local p;

        p := SmallestRootInt(q);

        if IsPrime(p) then 
            return p;
        else 
            return fail;
        fi;
    end );

InstallMethod(ConjugationHomomorphism, "generic method",
    [IsGroup, IsGroup, IsObject],
    function(A, B, g)
        return GroupHomomorphismByFunction(A, B, x -> x^g);
    end );
    
InstallMethod(Automizer, "for an overgroup",
    [IsGroup, IsGroup],
    function(G, H)
        local NGH, L, AutGH;

        if IsGroupOfAutomorphisms(G) then 
            return Automizer(G, H);
        fi;

        NGH := Normalizer(G, H);
        if IsTrivial(NGH) then 
            return Group(IdentityMapping(H));
        fi;

        L := List(GeneratorsOfGroup(NGH), a -> ConjugatorAutomorphismNC(H, a));
        if IsEmpty(L) then 
            return Group(IdentityMapping(H));
        fi;

        AutGH := Group(L);
        SetIsGroupOfAutomorphisms(AutGH, true);

        return AutGH;
    end );

InstallOtherMethod(Automizer, "for automorphism overgroup",
    [IsGroupOfAutomorphisms, IsGroup],
    function(Auts, H)
        local G, A, f1, f2, fAuts, fH, AutfAH, AutAH;

        G := Source(Identity(Auts));
        if not IsSubset(G, H) then 
            return Group(IdentityMapping(H));
        fi;

        A := SemidirectProduct(Auts, G);
        f1 := Embedding(A, 1);
        f2 := Embedding(A, 2);
        
        fAuts := Image(f1);
        fH := Image(f2, H);

        AutfAH := Automizer(fAuts, fH);
        AutAH := OnAutGroupConjugation(AutfAH, RestrictedInverseGeneralMapping(f2));
        SetIsGroupOfAutomorphisms(AutAH, true);

        return AutAH;
    end );

InstallMethod(NPhi, "generic method",
    [IsGroup, IsGroupHomomorphism],
    function(P, phi)
        local Q, R, CPQ, NPQ, AutPR, NPhiGens, QCPQ, g, N;

        Q := Source(phi);
        R := Image(phi);

        CPQ := Centralizer(P, Q);
        NPQ := Normalizer(P, Q);
        AutPR := Automizer(P, R);

        NPhiGens := Union(GeneratorsOfGroup(Q), GeneratorsOfGroup(CPQ));
        QCPQ := Group(NPhiGens);

        # Transverse NPQ in QCPQ and find all those g such that c_g^\phi \in \Aut_P(R)
        for g in RightTransversal(NPQ, QCPQ) do 
            if not g in Group(NPhiGens) and ConjugatorAutomorphismNC(P, g)^phi in AutPR then 
                Add(NPhiGens, g);

                if Group(NPhiGens) = NPQ then 
                    return NPQ;
                fi;
            fi;
        od;

        return Group(NPhiGens);
    end );

InstallMethod(AutomizerHomomorphism, "generic method",
    [IsGroup, IsGroup],
    function(G, H)
        local NGH, CGH, Aut;

        NGH := Normalizer(G, H);
        CGH := Centralizer(G, H);
        
        Aut := Automizer(G, H);

        return GroupHomomorphismByFunction(NGH, Aut, 
            g -> ConjugatorAutomorphismNC(H, g), 
            false, psi -> First(RightTransversal(NGH, CGH), g -> ConjugatorAutomorphismNC(H, g) = psi));
    end );

InstallMethod(PResidue, "generic method", 
    [IsGroup, IsPosInt],
    function (G, p)
        return NormalClosure(G, SylowSubgroup(G,p));
    end );

InstallMethod(IsRestrictedHomomorphism, "generic method",
    [IsGroupHomomorphism, IsGroupHomomorphism],
    function(psi, phi)
        local G, H, GensH, x;

        G := Source(phi);
        H := Source(psi);

        Assert(0, IsSubset(G, H));

        if not IsFinitelyGeneratedGroup(H) then 
            TryNextMethod();
        fi;

        # Check they both map the generators of H to the same set
        GensH := GeneratorsOfGroup(H);

        for x in GensH do 
            if phi(x) <> psi(x) then 
                return false;
            fi;
        od;
        
        return true;
    end );

InstallMethod(FindHomExtension, "generic method",
    [IsGroupHomomorphism, IsCollection],
    function(phi, L)
        return First(L, psi -> IsRestrictedHomomorphism(phi, psi));
    end );

InstallMethod(ExtendAut, "generic method",
    [IsGroupHomomorphism, IsGroupOfAutomorphisms],
    function(phi, A)
        local L, L0, C, psi, psi0;
        
        L := GeneratorsOfGroup(Source(phi));
        L0 := List(L, x -> Image(phi, x));
        
        return RepresentativeAction(A, L, L0, OnImageTuples);

        # psi := RepresentativeAction(A, L, L0, OnImageTuples);
        # if psi = fail then 
        #     return fail;
        # elif Order(psi) = Order(phi) then 
        #     return psi;
        # fi;
        # C := Stabilizer(A, L, OnImageTuples);
        # psi0 := First(RightCoset(C, psi), psi -> Order(psi) = Order(phi));
        # if psi0 <> fail then 
        #     return psi0;
        # else 
        #     return psi;
        # fi;
    end );

InstallMethod(PrCore, "generic method",
    [IsGroup, IsPosInt],
    function(G, p)
        local N, n;

        N := NormalSubgroups(G);
        N := Filtered(N, x -> PValuation(Size(x), p) = 0);
        n := Maximum(List(N, Size));

        return First(N, A -> Order(A) = n);
    end);
    
InstallMethod(HasStronglyPEmbeddedSub, "generic method",
    [IsGroup, IsPosInt],
    function(H, p)
        local S, O, n, q, q0;
        
        S := SylowSubgroup(H, p);
        q := Size(S);
        n := PValuation(q, p);
        
        if IsTrivial(S) or not IsTrivial(PCore(H,p)) then 
            return false;
        fi;
        
        # Based on [Sa14, Theorem 6.4]
        if IsCyclic(S) or IsQuaternionGroup(S) then 
            return true;
        fi;

        O := PResidue(H/PrCore(H, p), p);
        
        # (a) PSL(2, p^n)
        if Size(O) = q*(q+1)*(q-1)/Gcd(2,q-1) and IsSimpleGroup(O) then 
            return true;
        fi;

        # (b) PSU(3, p^n)
        if n mod 3 = 0 then 
            q0 := p^(n/3);
            if Size(O) = q0*(q0^2-1)*(q0^3+1)/Gcd(3,q0+1) and IsSimpleGroup(O) then 
                return true;
            fi;
        fi;

        if p = 2 then 
            # (a) PSL(2, 2)
            if Size(O) = 6 and IsSymmetricGroup(O) then 
                return true;
            fi;

            # (c) Sz(2^(2n+1)) for p = 2 and n ≥ 1
            if n-2 mod 4 = 0 then 
                q0 := 2^(q/2);
                if Size(O) = q0^2*(q0+1)*(q0-1) and IsSimpleGroup(O) then 
                    return true;
                fi;
            fi;
        fi;

        if p = 3 then 
            # (a) PSL(2, 3)
            if Size(O) = 12 and IsAlternatingGroup(O) then 
                return true;
            fi;

            # (d) '2G2(3^(2n+1)) for p = 3 and n ≥ 1
            if n-3 mod 6 = 0 then 
                q0 := 3^(q/3);
                if Size(O) = q0^3*(q0^3+1)*(q0-1) and IsSimpleGroup(O) then 
                    return true;
                fi;
            fi;

            # (f) PSL(3, 4), M11 for p = 3
            if Size(O) in [7920, 20160] and IsSimpleGroup(O) then 
                return true;
            fi;
        fi;

        if p >= 5 then 
            # (e) Alt(2p) for p ≥ 5,
            if Size(O) = Factorial(2*p) and IsAlternatingGroup(O) then 
                return true;
            fi;
        fi;

        if p = 5 then 
            # (g) Aut(Sz(32)), 2F4(2)′, McL, Fi22 for p = 5,
            if Size(O) in [17971200, 898128000, 64561751654400] and IsSimpleGroup(O) then 
                return true;
            elif Size(O) = 162688000 and IsAlmostSimpleGroup(O) then 
                return true;
            fi;
        fi;

        if p = 11 then 
            # (h) J4 for p = 11
            if Size(O) = 86775571046077562880 and IsSimpleGroup(O) then 
                return true;
            fi;
        fi;

        return false;
    end );

DescendReps := function(x, P, G)
    local T, N, L;
    
    if not IsSubnormal(G, P) then 
        Error("P must be subnormal in G");
    fi;

    T := P;
    while T <> G do 
        N := Normalizer(G,T);
        L := Orbit(N, x^T, OnCoCle(T));
        L := List(L, Representative);
        T := N;
    od;

    return L;
end;

AscendReps := function(L, G, P)
    local T, N;
    
    if not IsSubnormal(G, P) then 
        Error("P must be subnormal in G");
    fi;

    T := P;
    while T <> G do 
        N := Normalizer(G,T);
        L := Orbits(N, List(L, A -> A^T), OnCoCle(T));
        L := List(L, A -> Representative(Representative(A)));
        T := N;
    od;

    return L;
end;
