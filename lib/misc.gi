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

InstallGlobalFunction(OnImageNM, function(f)
    return function(x, phi)
        return Image(PreImagesRepresentative(f, phi), x);
    end;
end );

InstallGlobalFunction(OnImageTuples, function(L, phi)
    return List(L, x -> Image(phi, x));
end );

InstallGlobalFunction(OnImageTuplesNM, function(f) 
    return function(L, phi)
        return List(L, x -> Image(PreImagesRepresentative(f, phi), x));
    end;
end );

InstallGlobalFunction(OnHomConjugation, function(phi, psi)
    local A, # source of phi
          B, # range of phi
          B0, # psi(B)
          A0, # psi(A)
          psiA, # restriction of psi B -> B0
          psi1, # psi^-1
          psiB; # restriction of psi^-1 A0 -> A

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
    Assert(0, IsSubset(Source(psi), AutomorphismDomain(A)));

    if IsTrivial(A) then 
        B := Group(IdentityMapping(Image(psi, AutomorphismDomain(A))));
    else 
        B := Group(OnHomListConjugation(GeneratorsOfGroup(A), psi));
    fi;

    if HasSize(Kernel(psi)) and HasSize(A) then 
        SetSize(B, Size(A)/Size(Kernel(psi)));
    fi;

    return B;
end );

InstallGlobalFunction(OnCoCl, function(P)
    return function(x, phi)
        return Image(phi, Representative(x))^P;
    end;
end );

InstallGlobalFunction(OnCoClNM, function(P, f)
    return function(x, phi)
        return Image(PreImagesRepresentative(f, phi), Representative(x))^P;
    end;
end );

InstallGlobalFunction(OnCoCle, function(P)
    return function(x, a)
        return (Representative(x)^a)^P;
    end;
end );

InstallMethod(RestrictedHomomorphismNC, "generic method",
    [IsGroupHomomorphism, IsGroup, IsGroup],
    function(phi, A, B)
        local AGens, ImageAGens;
    
        AGens := GeneratorsOfGroup(A);
        ImageAGens := List(AGens, a -> Image(phi, a));
        return GroupHomomorphismByImagesNC(A, B, AGens, ImageAGens);
    end);

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
    
InstallMethod(Automizer, "for an overgroup",
    [IsGroup, IsGroup],
    function(G, H)
        local NGH, # normalizer of H in G
              CGH, # centralizer of H in G
              q, # homomorphism from NGH to the quotient NGH/CGH
              L, # the generators of NGH/CGH
              L0, # the generators of AutGH
              AutGH,
              n; # the nice monomorphism

        if IsGroupOfAutomorphisms(G) then 
            return Automizer(G, H);
        fi;

        NGH := Normalizer(G, H);
        CGH := Centralizer(G, H);
        q := NaturalHomomorphismByNormalSubgroup(NGH, CGH);
        
        L := GeneratorsOfGroup(Image(q));
        if IsEmpty(L) then 
            L := [IdentityMapping(Image(q))];
        fi;
        L0 := List(L, a -> ConjugatorAutomorphismNC(H, PreImagesRepresentative(q, a)));
        AutGH := Group(L0);
        
        n := GroupHomomorphismByImages(AutGH, Image(q));
        Assert(0, n <> fail);

        SetNiceMonomorphism(AutGH, n);
        SetIsGroupOfAutomorphisms(AutGH, true);

        return AutGH;
    end );

InstallOtherMethod(Automizer, "for automorphism overgroup",
    [IsGroupOfAutomorphisms, IsGroup],
    function(Auts, H)
        local G, # the domain of Auts
              f, # the nice monomorphism   
              NGA, # the normalizer of H in Auts
              CGA, # the centralizer of H in Auts
              q, # the quotient homomorphism NGA -> NGA/CGA
              L, # the generators of Image(q)
              L0, # the generators of AutGH
              AutGH, 
              n; # the nice monomorphism

        G := AutomorphismDomain(Auts);
        if not IsSubset(G, H) then 
            return Group(IdentityMapping(H));
        elif G = H then 
            return Auts;
        fi;

        f := NiceMonomorphism(Auts);
        NGA := Stabilizer(Image(f, Auts), H, OnImageNM(f));
        CGA := Kernel(ActionHomomorphism(Image(f, Auts), H, OnImageNM(f)));
        q := NaturalHomomorphismByNormalSubgroup(NGA, CGA);
        
        L := GeneratorsOfGroup(Image(q));
        if IsEmpty(L) then 
            L := [IdentityMapping(Image(q))];
        fi;
        L0 := List(L, a -> RestrictedHomomorphismNC(PreImagesRepresentative(f, PreImagesRepresentative(q, a)), H, H));
        AutGH := Group(L0);
        
        n := GroupHomomorphismByImages(AutGH, Image(q));
        Assert(0, n <> fail);

        SetNiceMonomorphism(AutGH, n);
        SetIsGroupOfAutomorphisms(AutGH, true);

        return AutGH;
    end );

InstallMethod(NPhi, "generic method",
    [IsGroup, IsGroupHomomorphism],
    function(S, phi)
        local A, B, CSA, NSA, AutSB, ACSA;

        A := Source(phi);
        B := Image(phi);

        CSA := Centralizer(S, A);
        NSA := Normalizer(S, A);
        AutSB := Automizer(S, B);

        ACSA := ClosureGroup(A, CSA);

        return FindSubgroup(NSA, g -> ConjugatorAutomorphismNC(S, g)^phi in AutSB, ACSA);
    end );

InstallMethod(ExtendAut, "generic method",
    [IsGroupHomomorphism, IsGroupOfAutomorphisms],
    function(phi, A)
        local L, L0, f, x;
        
        L := GeneratorsOfGroup(Source(phi));
        L0 := List(L, x -> Image(phi, x));

        f := NiceMonomorphism(A);
        x := RepresentativeAction(Image(f,A), L, L0, OnImageTuplesNM(f));

        if x = fail then 
            return fail;
        fi;

        return PreImage(f,x);
    end );

InstallMethod(PResidue, "generic method", 
    [IsGroup, IsPosInt],
    function (G, p)
        return NormalClosure(G, SylowSubgroup(G,p));
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
    
InstallMethod(HasStronglyPEmbeddedSubgroup, "generic method",
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

InstallGlobalFunction(DescendReps, function(x, P, G)
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
    end );

InstallGlobalFunction(AscendReps, function(L, G, P)
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
    end );

InstallGlobalFunction(FindSubgroup, function(arg)
    local G, # the group
          f, # the property
          H, # the subgroup to be found
          i, # counter
          T, # transversal of G in H
          C; # a copy of all checked cosets
    
    if not Length(arg) in [2,3] then 
        Error("Invalid usage");
    else
        G := arg[1];
        f := arg[2];
        if Length(arg) = 3 then 
            H := arg[3];
        else 
            H := TrivialSubgroup(G);
        fi;
    fi;

    i := 2;
    T := RightTransversal(G, H);
    C := [];

    while i <= Length(T) do 
        if ForAll(C, a -> not T[i] in a) and f(T[i]) then
            H := ClosureGroup(H, T[i]); 
            i := 2;
            T := RightTransversal(G, H);
        else 
            Add(C, RightCoset(H, T[i]));
            i := i+1;
        fi;
    od;
    
    return H;
end);

InstallMethod(FindMaxNPhi, "generic method",
    [IsGroup, IsGroupOfAutomorphisms],
    function(S, X)
        local A, # the domain of X
              f, # a nice monomorphism from X
              NSA, # normalizer of S in A
              AutSA, 
              T; # the subgroup

        A := AutomorphismDomain(X);
        f := NiceMonomorphism(X);

        NSA := Normalizer(S, A);
        AutSA := Automizer(S, A);
        AutSA := Image(f, AutSA);
        T := FindSubgroup(Image(f, X), phi -> NPhi(S, PreImagesRepresentative(f, phi))=NSA, AutSA);

        return PreImage(f, T);
    end );
