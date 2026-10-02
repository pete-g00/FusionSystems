# Produces a list of numbers using which the isomorphism type 
# of the group G can be almost completely inferred.
# If G is small enough to support IdGroup, then we only rely on that (i.e. [size of G, isom id of G])
# 
# Otherwise, we make use of the following values:
# - Size of G
# - Size of the center of G
# - Size of the derived subgroup of G
# - Length of a composition series of G
# - Exponent of G
# - Length of the maximal subgroups of G (up to conjugacy classes)
# - (for p-groups) Rank of G
IsomType := function(G)
    if IdGroupsAvailable(Size(G)) then 
        return IdGroup(G);
    fi;

    if IsPrimePowerInt(Size(G)) then 
        return [
            Size(G),
            Size(Center(G)),
            Size(DerivedSubgroup(G)),
            NilpotencyClassOfGroup(G),
            Length(CompositionSeries(G)),
            Exponent(G),
            Length(MaximalSubgroupClassReps(G)),
            Rank(G)
        ];
    else 
        return [
            Size(G),
            Size(Center(G)),
            Size(DerivedSubgroup(G)),
            NilpotencyClassOfGroup(G),
            Length(CompositionSeries(G)),
            Exponent(G),
            Length(MaximalSubgroupClassReps(G))
        ];
    fi;
end;

# Returns a number that compares the isomorphism type of A with the isomorphism type of B
# Essentially, this is IsomType(A) - IsomType(B)
# So, if the value is 0, then the two groups have the same IsomType value
# If the value is -ve then A and B don't have the same IsomType value, and the first value that is different is where A has a smaller number than B
# The opposite is the case when the value is +ve
CompareByIsom := function(A, B)
    local IsomTypeA, IsomTypeB, i, sub;

    IsomTypeA := IsomType(A);
    IsomTypeB := IsomType(B);

    for i in [1..Length(IsomTypeA)] do 
        sub := IsomTypeA[i] - IsomTypeB[i];
        if sub <> 0 then 
            return sub;
        fi;
    od;

    return 0;
end;

# Groups a list of subgroups by IsomType
# Returns a record labelled by the isomtypes (a stringified version of the list)
# and entries the subgroups given that belong to the isomtype
GroupByIsomType := function(L)
    local Subs, i, C, Q, Cons, R, label;

    L := ShallowCopy(L);
    Sort(L, function(A, B)
        return CompareByIsom(A, B) <= 0;
    end );
    
    Subs := rec();
    i := 1;

    while i <= Length(L) do
        Q := L[i];
        Cons := [Q];
            
        while i+1 <= Length(L) and CompareByIsom(Q, L[i+1]) = 0 do 
            i := i+1;
            R := L[i];
            Add(Cons, R);
        od; 

        i := i+1;
        label := String(IsomType(Q));
        Subs.(label) := Cons;
    od;
    
    return Subs;
end;

InstallMethod(FClassesReps, "generic method",
    [IsFusionSystem],
    function(F)
        return List(FClasses(F), Representative);
    end );

InstallMethod(FClassReps, "generic method",
    [IsFusionSystem, IsGroup],
    function(F, A)
        return Reps(FClass(F,A));
    end );

InstallMethod(ViewObj, "generic method",
    [IsFusionSystem], 0,
    function(F)
        Print("Fusion System on ", ViewString(UnderlyingGroup(F)));
    end );

InstallMethod(AreFConjugate, "generic method",
    [IsFusionSystem, IsGroup, IsGroup],
    function (F, A, B) 
        return RepresentativeFIsomorphism(F, A, B) <> fail;
    end );

InstallMethod(\in, "generic method",
    [IsGroupHomomorphism, IsFusionSystem],
    function (phi, F)
        local A, B, psi;

        if not IsInjective(phi) then 
            return false;
        fi;
        
        A := Source(phi);
        B := Range(phi);
        
        if not (IsSubset(UnderlyingGroup(F), A) or IsSubset(UnderlyingGroup(F), B)) then 
            return false;
        fi;

        B := Image(phi);
        psi := RepresentativeFIsomorphism(F, B, A);

        if psi = fail then 
            return false;
        fi;
        
        # phi: A -> B, psi: B -> A
        # phi lies in Isom(A, B) <=> phi*psi lies in AutF(A)
        return phi*psi in AutF(F, A);
    end );

InstallMethod(IsFullyNormalized, "generic method",
    [IsFusionSystem, IsGroup],
    function(F, Q)
        local P, NPQ;

        P := UnderlyingGroup(F);
        NPQ := Normalizer(P, Q);

        if NPQ = P then 
            return true;
        fi;

        return ForAll(FClassReps(F, Q), R -> Size(NPQ) >= Size(Normalizer(P, R)));
    end );

InstallMethod(IsFullyCentralized, "generic method",
    [IsFusionSystem, IsGroup],
    function(F, Q)
        local P, CPQ;

        P := UnderlyingGroup(F);
        CPQ := Centralizer(P, Q);

        if CPQ = P then 
            return true;
        fi;

        return ForAll(FClassReps(F, Q), R -> Size(CPQ) >= Size(Centralizer(P, R)));
    end );

InstallMethod(IsFullyAutomized, "generic method",
    [IsFusionSystem, IsGroup],
    function(F, Q)
        local AutPQ, AutFQ, p;

        # Check $Aut_P(Q)$ is a Sylow-$p$ subgroup of $Aut_F(Q)$
        AutFQ := AutF(F, Q);
        AutPQ := Automizer(UnderlyingGroup(F), Q);
        p := Prime(F);

        return PValuation(Size(AutPQ), p) = PValuation(Size(AutFQ), p);
    end );

InstallMethod(ExtendMapToNPhi, "generic method",
    [IsFusionSystem, IsGroupHomomorphism],
    function(F, phi)
        local A, B, N, NPB, AutFN, L, X, psi, psiB, psi1, a;

        A := Source(phi);
        B := Image(phi);
        
        N := NPhi(UnderlyingGroup(F), phi);
        if N = A then 
            return phi;
        fi;
        NPB := Normalizer(UnderlyingGroup(F), B);
        
        AutFN := AutF(F, N);
        L := ContainedFConjugates(F, N, NPB);

        for X in L do 
            if IsSubset(X, B) then 
                psi := RepresentativeFIsomorphism(F, X, N);
                psiB := RestrictedMapping(psi, B);
                psi1 := InverseGeneralMapping(psi);
                a := ExtendAut(phi*psiB, AutFN);
                if a <> fail then 
                    return a*psi1;
                fi;
            fi;
        od;

        return fail;
    end );

InstallMethod(IsFReceptive, "generic method",
    [IsFusionSystem, IsGroup],
    function (F, Q)
        local AutPQ, AutFQ, OutFQ;

        if Q = UnderlyingGroup(F) then 
            return true;
        fi;
        
        AutPQ := Automizer(UnderlyingGroup(F), Q);
        AutFQ := AutF(F, Q);

        # Check for every F-isomorphism R -> Q can be extended to N_\phi
        # TODO: Figure out a way to make fewer checks
        return ForAll(FClassReps(F, Q), 
            R -> ForAll(IsomF(F, R, Q), phi -> ExtendMapToNPhi(F, phi) <> fail));
    end );

InstallMethod(IsSaturated, "generic method",
    [IsFusionSystem],
    function(F)
        local C, Cls;
        
        C := FClassesReps(F);
        Cls := List(C, Q -> FClassReps(F, Q));

        # Check whether every F-class contains a fully automized member (for efficiency),
        # and if a subgroup is fully normalized, then it is receptive
        # TODO: Figure out a way to make fewer checks
        return ForAll([1..Length(C)], i -> ForAny(Cls[i], R -> IsFullyAutomized(F, R))) and
            ForAll([1..Length(C)], i -> ForAll(Cls[i], R -> not IsFullyNormalized(F, R) or IsFReceptive(F, R)));
    end );

InstallMethod(IsFCentric, "generic method",
    [IsFusionSystem, IsGroup],
    function(F, Q)
        return ForAll(FClassReps(F, Q), 
            R -> IsSubset(R, Centralizer(UnderlyingGroup(F), R)));
    end );

InstallMethod(IsFRadical, "generic method",
    [IsFusionSystem, IsGroup],
    function(F, Q)
        return PCore(AutF(F, Q), Prime(F)) = Automizer(Q,Q);
    end );

InstallMethod(IsFEssential, "generic method",
    [IsFusionSystem, IsGroup],
    function(F, Q)
        local InnQ, AutFQ, OutFQ;

        if not IsFCentric(F, Q) then 
            return false;
        fi;

        if IsCyclic(Q) then 
            return false;
        fi;

        InnQ := Automizer(Q,Q);
        AutFQ := AutF(F, Q);
        OutFQ := AutFQ/InnQ;

        return HasStronglyPEmbeddedSub(OutFQ, Prime(F));
    end );

InstallMethod(\=, "generic method",
    [IsFusionSystem, IsFusionSystem],
    function(F, E)
        local C;

        if IsIdenticalObj(F, E) then 
            return true;
        fi;

        if UnderlyingGroup(F) <> UnderlyingGroup(E) then 
            return false;
        fi;

        # compute the E-conjugacy classes and check they are the same as classes in F
        # check whether the size of the automorphism groups match and the F-classes
        # TODO: Might be simpler to just check using P-cocl (which may be faster to compute?)
        C := FClassesReps(F);

        # (checking AutF is faster than FClass in general)
        return 
            ForAll(FClassesReps(F), Q -> AutF(F, Q) = AutF(E, Q)) and
            ForAll(FClassesReps(F), Q -> FClass(F, Q) = FClass(E, Q));
    end );

InstallMethod(IsomorphismFusionSystems, "generic method",
    [IsFusionSystem, IsFusionSystem],
    function(F, E)
        local P1, P2, phi, Auts, psi, sigma;

        if IsIdenticalObj(F, E) then 
            return IdentityMapping(UnderlyingGroup(F));
        fi;

        # try to find an isomorphism between the 2 groups
        P1 := UnderlyingGroup(F);
        P2 := UnderlyingGroup(E);

        phi := IsomorphismGroups(P1, P2);

        if phi = fail then 
            return fail;
        fi;

        Auts := AutomorphismGroup(P1);
        
        # any map in automorphism of P1 (as a fusion system) won't yield us anything, so we can transverse it
        for psi in RightTransversal(Auts, AutF(F, P1)) do 
            sigma := psi*phi;
            if F^sigma = E then 
                return sigma;
            fi;
        od;

        return fail;
    end );
