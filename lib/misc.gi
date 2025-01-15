InstallMethod(IsomType, "generic method",
    [IsGroup],
    function(A)
        local LCS, UCS, DS;

        if IdGroupsAvailable(Size(A)) then 
            return IdGroup(A);
        fi;

        LCS := LowerCentralSeries(A);
        UCS := UpperCentralSeries(A);
        DS := DerivedSeries(A);
        
        return [
            Size(A),
            Exponent(A),
            AbelianInvariants(A),
            List(LCS{[2..Length(LCS)]}, IsomType),
            List(UCS{[2..Length(UCS)]}, IsomType),
            List(DS{[2..Length(DS)]}, IsomType),
            IsomType(FrattiniSubgroup(A))
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
    local B, x;

    Assert(0, IsGroupOfAutomorphisms(A));
    Assert(0, IsGroupHomomorphism(psi));
    Assert(0, IsSubset(Source(psi), AutomorphismDomain(A)));

    if IsTrivial(A) then
        A := Group(IdentityMapping(AutomorphismDomain(A))); 
        B := Group(IdentityMapping(Image(psi, AutomorphismDomain(A))));
    else 
        B := Group(OnHomListConjugation(GeneratorsOfGroup(A), psi));
    fi;
    
    if not HasNiceMonomorphism(A) then 
        AssignNiceMonomorphismAutomorphismGroup(A, AutomorphismDomain(A));
    fi;
    x := GroupHomomorphismByImages(B, A);
    x := x*NiceMonomorphism(A);

    SetNiceMonomorphism(B, x);
    SetIsInjective(x, true);
    SetFilterObj(x, IsNiceMonomorphism);
    SetIsHandledByNiceMonomorphism(B, true);
    SetIsGroupOfAutomorphisms(B, true);

    return B;
end );

InstallGlobalFunction(OnCoCl, function(P)
    return function(x, phi)
        return Image(phi, Representative(x))^P;
    end;
end );

InstallGlobalFunction(OnCoCle, function(P)
    return function(x, g)
        return (Representative(x)^g)^P;
    end;
end );

InstallGlobalFunction(OnCoClNM, function(P, f)
    return function(x, phi)
        return Image(PreImagesRepresentative(f, phi), Representative(x))^P;
    end;
end );

InstallGlobalFunction(OnCoClTuples, function(P)
    return function(L, phi)
        return List(L, x -> Image(phi, Representative(x))^P);
    end;
end );

InstallGlobalFunction(OnCoClTuplesNM, function(P, f)
    return function(L, phi)
        return List(L, 
            x -> Image(PreImagesRepresentative(f, phi), Representative(x))^P);
    end;
end );

InstallGlobalFunction(RestrictedHomomorphismNC, function(arg)
        local phi, A, B, AGens, ImageAGens;

        phi := arg[1];
        A := arg[2];

        if Length(arg) = 3 then 
            B := arg[3];
        else 
            B := Image(phi, A);
        fi;
    
        AGens := GeneratorsOfGroup(A);
        ImageAGens := List(AGens, a -> Image(phi, a));
        return GroupHomomorphismByImagesNC(A, B, AGens, ImageAGens);
    end);

InstallGlobalFunction(RestrictedHomomorphism, function(arg)
        local phi, A, B, P, Q;

        phi := arg[1];
        A := arg[2];

        P := Source(phi);
        if not IsSubset(P, A) then 
            Error("A is not a subgroup of the domain.");
        fi;

        if Length(arg) = 3 then 
            B := arg[3];
            Q := Image(phi, A);
            if not IsSubset(B, Q) then 
                Error("The codomain is not a subgroup of B.");
            fi;
        else 
            B := Image(phi, A);
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
            L := [Identity(Image(q))];
        fi;
        L0 := List(L, a -> ConjugatorAutomorphismNC(H, PreImagesRepresentative(q, a)));
        AutGH := Group(L0);
        
        n := GroupHomomorphismByImages(AutGH, Image(q), L0, L);
        Assert(0, n <> fail);

        SetNiceMonomorphism(AutGH, n);
        SetIsInjective(n, true);
        SetFilterObj(n, IsNiceMonomorphism);
        SetIsHandledByNiceMonomorphism(AutGH, true);
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

        if not HasNiceMonomorphism(Auts) then 
            AssignNiceMonomorphismAutomorphismGroup(Auts, G);
        fi;

        f := NiceMonomorphism(Auts);
        NGA := Stabilizer(Image(f, Auts), H, OnImageNM(f));
        CGA := Kernel(ActionHomomorphism(NGA, H, OnImageNM(f)));
        q := NaturalHomomorphismByNormalSubgroup(NGA, CGA);
        
        L := GeneratorsOfGroup(Image(q));
        if IsEmpty(L) then 
            L := [Identity(Image(q))];
        fi;
        L0 := List(L, a -> RestrictedHomomorphismNC(PreImagesRepresentative(f, PreImagesRepresentative(q, a)), H, H));
        AutGH := Group(L0);
        
        n := GroupHomomorphismByImages(AutGH, Image(q), L0, L);
        Assert(0, n <> fail);
        
        SetNiceMonomorphism(AutGH, n);
        SetIsInjective(n, true);
        SetFilterObj(n, IsNiceMonomorphism);
        SetIsHandledByNiceMonomorphism(AutGH, true);
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
        local L, L0, n, x;
        
        L := GeneratorsOfGroup(Source(phi));
        L0 := List(L, x -> Image(phi, x));

        if not HasNiceMonomorphism(A) then 
            AssignNiceMonomorphismAutomorphismGroup(A, AutomorphismDomain(A));
        fi;

        n := NiceMonomorphism(A);
        x := RepresentativeAction(Image(n,A), L, L0, OnImageTuplesNM(n));

        if x = fail then return fail; fi;
        return PreImagesRepresentative(n,x);
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

InstallMethod(NormalizerChain, "generic method",
    [IsGroup, IsGroup],
    function(A, B)
        local N;
        
        if not (IsSubnormal(B, A) and IsSubset(B, A)) then 
            Error("A must be a subnormal subgroup of B");
        fi;

        N := [A];
        while N[Length(N)] <> B do 
            Add(N, Normalizer(B, N[Length(N)]));
        od;

        return N;
    end );

InstallGlobalFunction(DescendReps, function(x, P, G)
    local N, L, i;

    if Size(x^G) < 500 or not (IsSubnormal(G, P) and IsSubset(G, P)) then 
        L := Orbits(P, x^G);
        return List(L, Representative);
    fi;

    N := NormalizerChain(P, G);
    L := [x];
    for i in [1..Length(N)-1] do
        L := List(L, A -> A^N[i]); 
        L := Flat(Orbits(N[i+1], L, OnCoCle(N[i])));
        L := List(L, Representative);
    od;

    return L;
end );

InstallGlobalFunction(AscendReps, function(L, G, P)
    local D, N, i;
    
    if Sum(List(L, A -> Size(A^P))) < 500 or not (IsSubnormal(G, P) and IsSubset(G, P)) then 
        D := Flat(List(L, A -> AsList(A^P)));
        L := Orbits(G, D);
        return List(L, Representative);
    fi;
    
    N := NormalizerChain(P, G);
    for i in [1..Length(N)-1] do
        L := List(L, A -> A^N[i]); 
        L := Orbits(N[i+1], L, OnCoCle(N[i]));
        L := List(L, A -> Representative(Representative(A)));
    od;

    return L;
end );

InstallGlobalFunction(AscendRepsAutomorphismGroup, function(L, A)
    local P, n;

    P := AutomorphismDomain(A);
    
    if not HasNiceMonomorphism then 
        AssignNiceMonomorphismAutomorphismGroup(A, P);
    fi;

    n := NiceMonomorphism(A);
    L := Orbits(Image(n,A), List(L, X -> X^P), OnCoClNM(P,n));
    return List(L, X -> Representative(Representative(X)));
end );

InstallGlobalFunction(DescendRepsAutomorphismGroup, function(x, A)
    local P, n, L;

    P := AutomorphismDomain(A);
    
    if not HasNiceMonomorphism then 
        AssignNiceMonomorphismAutomorphismGroup(A, P);
    fi;
    
    n := NiceMonomorphism(A);
    L := Orbit(Image(n,A), x^P, OnCoClNM(P,n));
    return List(L, Representative);
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
        if not HasNiceMonomorphism(X) then 
            AssignNiceMonomorphismAutomorphismGroup(X, A);
        fi;
        f := NiceMonomorphism(X);

        NSA := Normalizer(S, A);
        AutSA := Automizer(S, A);
        AutSA := Image(f, AutSA);
        T := FindSubgroup(Image(f, X), phi -> NPhi(S, PreImagesRepresentative(f, phi))=NSA, AutSA);

        return PreImage(f, T);
    end );

# InstallOtherMethod(ContainingConjugates, "for semidirect product",
#     [IsGroup, IsGroupOfAutomorphisms, IsGroup, IsGroup],
#     function(S, C, A, B)
#         local L0, n, L, X, St, R, x, X0, i, f;

#         L0 := ContainingConjugates(S, A, B);

#         if not HasNiceMonomorphism(C) then 
#             AssignNiceMonomorphismAutomorphismGroup(C, S);
#         fi;

#         n := NiceMonomorphism(C);
#         L := Set([]);

#         for X in L0 do 
#             St := Stabilizer(Image(n,C), X[1], OnImageNM(n));
#             R := RightTransversal(Image(n,C), St);
#             for x in R do 
#                 X0 := OnImageNM(n)(X[1], x);
#                 i := PositionSortedBy(L, X0, First);

#                 if not i in [1..Length(L)] or L[i][1] <> X0 then 
#                     f := ConjugatorIsomorphism(B, X[2])*PreImage(n,x);
#                     AddSet(L, [X0, f]);
#                 fi;
#             od;
#         od;

#         return L;
#     end );

# InstallOtherMethod(ContainedConjugates, "for semidirect product",
#     [IsGroup, IsGroupOfAutomorphisms, IsGroup, IsGroup],
#     function(S, C, A, B)
#         local L0, n, L, X, St, R, x, X0, i, f;

#         L0 := ContainedConjugates(S, A, B);

#         if not HasNiceMonomorphism(C) then 
#             AssignNiceMonomorphismAutomorphismGroup(C, S);
#         fi;

#         n := NiceMonomorphism(C);
#         L := Set([]);

#         for X in L0 do 
#             St := Stabilizer(Image(n,C), X[1], OnImageNM(n));
#             R := RightTransversal(Image(n,C), St);
#             for x in R do 
#                 X0 := OnImageNM(n)(X[1], x);
#                 i := PositionSortedBy(L, X0, First);

#                 if not i in [1..Length(L)] or L[i][1] <> X0 then 
#                     f := ConjugatorIsomorphism(A, X[2])*PreImage(n,x);
#                     AddSet(L, [X0, f]);
#                 fi;
#             od;
#         od;

#         return L;
#     end );

InstallMethod(RepresentativesUpToClass, "generic method",
    [IsGroup, IsGroup, IsGroup],
    function(A, B, N)
        local C, L;

        C := A^B;
        
        if not IsSubnormal(N, B) and IsSubset(B, N) then 
            Error("N must be a subnormal subgroup in G");
        fi;

        if Size(C) < 5000 then 
            L := Orbit(N, C);
            return List(L, Representative);
        fi;

        L := NormalizerChain(A, B);
        

        # N0 := Normalizer(B,A);

        # while N0 <> B do 
            
        # od;

        # if IsGroupOfAutomorphisms(B) and IsGroupOfAutomorphisms(N) then 
        #     RepresentativesUpToClass(A, B, N);
        # fi;

        # if not IsNormal(B, N) then 
        #     Error("N is not normal in B");
        # elif not IsSubset(B, A) then
        #     Error("A is not a subset of B");
        # fi;

        # L := Orbit(B, A^N);
        # return List(L, Representative);
    end );

# InstallOtherMethod(RepresentativesUpToClass, "for automorphisms",
#     [IsGroup, IsGroupOfAutomorphisms, IsGroupOfAutomorphisms],
#     function(A, B, N)
#         local G, n, L;
        
#         if AutomorphismDomain(B) <> AutomorphismDomain(N) then 
#             Error("The automorphism subgroups are not on the same group");
#         fi;

#         G := AutomorphismDomain(B);

#         n := NiceMonomorphism(B);
#         L := Orbit(Image(n,B), A^G, OnCoClNM(G,n));
        
#         n := NiceMonomorphism(N);
#         L := Orbits(Image(n,N), L, OnCoClNM(G,n));

#         return List(L, A -> Representative(Representative(A)));
#     end );

# finding a map A -> B in S : C, where $C \leq \Aut(S)$
RepresentativeActionSDProd := function(S, C, A, B)
    local n, a, Aa, f;

    if not HasNiceMonomorphism(C) then 
        AssignNiceMonomorphismAutomorphismGroup(C, S);
    fi;
    n := NiceMonomorphism(C);

    a := RepresentativeAction(Image(n,C), A^S, B^S, OnCoClNM(S,n));
    if a = fail then 
        return fail;
    fi;

    a := PreImagesRepresentative(n, a);
    Aa := Image(a, A);
    f := ConjugatorIsomorphism(Aa, RepresentativeAction(S, Aa, B));

    return RestrictedHomomorphism(a, A, Aa)*f;
end;

ContainedConjugatesSDProd := function(arg)
    local InitializeRep, S, C, A, B, onlyone, n, L, St, T, t, D, L0, l, x;

    S := arg[1];
    C := arg[2];
    A := arg[3];
    B := arg[4];

    onlyone := Length(arg) = 4 or arg[5];

    if not HasNiceMonomorphism(C) then 
        AssignNiceMonomorphismAutomorphismGroup(C, S);
    fi;
    n := NiceMonomorphism(C);

    if IsSubset(A, B) and onlyone then 
        return [B, IdentityMapping(B)];
    fi;

    L := [];
    St := Stabilizer(Image(n,C), A^S, OnCoClNM(S,n));
    T := RightTransversal(Image(n,C), St);

    InitializeRep := function(t)
        local A0, a;

        t := PreImagesRepresentative(n, t);
        A0 := Image(t, A);
        a := ConjugatorIsomorphism(A, t);

        return [A0, a];
    end;
    
    for t in T do 
        D := InitializeRep(t);
        L0 := ContainedConjugates(S, D[1], B, onlyone);
        if onlyone and L0 <> fail then
            x := D[2]*ConjugatorIsomorphism(D[1], L0[2]);
            return [L0[1], x]; 
        else 
            for l in L0 do 
                x := D[2]*ConjugatorIsomorphism(D[1], l[2]);
                Add(L, [l[1], x]);
            od;
        fi;
    od;

    if onlyone then 
        return fail;
    else 
        return L;
    fi;
end;

# finds representatives of A^G containing B up to N-conjugacy
ContainedConjugatesDet := function(G, N, A, B)
    local L;

    L := ContainedConjugates(G, B, A, true);
    if L = fail then 
        return [];
    fi;

    L := DescendReps(L[1], N, G);
    return Filtered(L, A0 -> IsSubset(B, A0));
end;

ContainingConjugatesDet := function(G, N, A, B)
    local L;

    L := ContainedConjugates(G, B, A, true);
    if L = fail then 
        return [];
    fi;

    B := B^(L[2]^-1);
    L := DescendReps(B, N, G);
    return Filtered(L, B0 -> IsSubset(B0, A));
end;

ContainedConjugatesDetSDProd := function(G, X, N, A, B)
    local n, L;

    if not HasNiceMonomorphism(X) then 
        AssignNiceMonomorphismAutomorphismGroup(X, G);
    fi;

    n := NiceMonomorphism(X);
    L := Orbit(Image(n,X), A, OnImageNM(n));

    return Flat(List(L, A -> ContainedConjugatesDetSDProd(G, N, A, B)));
end;

ContainingConjugatesDetSDProd := function(G, X, N, A, B)
    local n, L;
    
    if not HasNiceMonomorphism(X) then 
        AssignNiceMonomorphismAutomorphismGroup(X, G);
    fi;

    n := NiceMonomorphism(X);
    L := Orbit(Image(n,X), B, OnImageNM(n));

    return Flat(List(L, B -> ContainedConjugatesDetSDProd(G, N, A, B)));
end;

ProbablyIsomorphic := function(A, B)
    local s, a, b, L;

    Assert(0, IsSolvable(A) and IsSolvable(B));
    if Size(A) <> Size(B) then return false; fi;
    
    s := Size(A);
    a := CodePcGroup(A);
    b := CodePcGroup(B);
    if a = b then return true; fi;

    L := [rec(code := a, order := s), rec(code := b, order := s)];
    L := RandomIsomorphismTest(L, 1);
    return Length(L) = 1;
end;
