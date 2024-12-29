InstallMethod(SaturatedFusionSystemNC, "for a group and a list of automizers",
    [IsGroup, IsList],
    function(S, L)
        local p, d, A, P, C, F, D;
        
        p := FindPrimeOfPrimePower(Size(S));
        Assert(0, p <> fail);
        Assert(0, ForAll(L, IsGroupOfAutomorphisms));

        d := [];
        for A in L do 
            P := AutomorphismDomain(A);
            C := Objectify(NewType(CollectionsFamily(FamilyObj(P)), IsFClassRep),
                rec(data := [rec(sub := P, map := IdentityMapping(P))]));
            SetRepresentative(C, P);
            SetAutF(C, A);
            Add(d, C);
        od;

        F := Objectify(NewType(FusionSystemFamily, IsSaturatedFusionSystemRep), rec());
        SetUnderlyingGroup(F, S);
        SetPrime(F, p);

        for D in d do 
            SetUnderlyingFusionSystem(D, F);
        od;
        F!.essclasses := Immutable(d);
        F!.knownclasses := Set(d);

        return F;
    end );

InstallOtherMethod(ViewObj, "generic method",
    [IsFusionSystem], 0,
    function(F)
        Print("Fusion System on ");
        ViewObj(UnderlyingGroup(F));
    end );

InstallOtherMethod(Automizer, "for a fusion system and a subgroup",
    [IsSaturatedFusionSystemRep, IsGroup],
    function(F, A)
        local C;

        C := FClass(F, A);
        return Automizer(C, A);
    end );

InstallMethod(RepresentativeFIsomorphism, "for a saturated fusion system and subgroups",
    [IsSaturatedFusionSystemRep, IsGroup, IsGroup],
    function(F, A, B)
        return FindMap(FClass(F,A), B);
    end );

InstallMethod(FClasses, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        local S, C, i, A, C0;

        S := UnderlyingGroup(F);
        Info(InfoFusion, 1, "Finding subgroups of S");
        C := ConjugacyClassesSubgroups(S);
        C := List(C, Representative);
        # TODO: Group up to Aut-F class
        
        i := Size(F!.knownclasses);
        Info(InfoFusion, 3, "Already know ", i, " classes");
        for A in C do 
            C0 := FClass(F,A);
            if i <> Size(F!.knownclasses) then 
                Info(InfoFusion, 3, "Found new class of size ", Size(C0), " on a group of order ", Size(Representative(C0)));
                i := i+1;
            fi;
        od;

        return Immutable(F!.knownclasses);
    end );

InstallMethod(CentricFClasses, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        local S, C, L, A, C0;

        S := UnderlyingGroup(F);
        Info(InfoFusion, 1, "Finding subgroups of S");
        
        C := ConjugacyClassesSubgroups(S);
        C := List(C, Representative);
        Info(InfoFusion, 2, "There are ", Length(C), " subgroups up to S-class");

        Info(InfoFusion, 1, "Filtering centric subgroups");
        C := Filtered(C, A -> Centralizer(S,A) = Center(A));
        Info(InfoFusion, 2, "There are ", Length(C), " centric subgroups up to S-class");
        
        L := Set([]);
        i := Length(L);
        for A in C do 
            C0 := FClass(F,A);
            if IsCentric(C0) then 
                AddSet(L, C0);
                if i <> Length(L) then 
                    Info(InfoFusion, 3, "Found new class of size ", Size(C0), " on a group of order ", Size(Representative(C0)));
                fi;
            fi;
            
            i := Length(L);
        od;

        return L;
    end );

InstallMethod(Core, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep], 
    function(F)
        local E, N, C, A, R, n;

        E := F!.essclasses;
        N := NormalSubgroups(UnderlyingGroup(F));
        for C in E do 
            R := Representative(C);
            N := Filtered(N, X -> IsSubset(R, X) and IsNormal(R, X));
            A := AutF(C);
            if not HasNiceMonomorphism(A) then 
                AssignNiceMonomorphismAutomorphismGroup(A, R);
            fi;
            n := NiceMonomorphism(AutF(C));
            N := Orbits(Image(n,A), N, OnImageNC(n));
            N := Filtered(N, X -> Size(X) = 1);
            N := List(N, Representative);
        od;

        n := Maximum(List(N, Size));
        return First(N, A -> Size(A) = n);
    end );

InstallMethod(FocalSubgroup, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        local T, E, C, R, Aut, T0;

        T := TrivialSubgroup(UnderlyingGroup(F));
        E := F!.essclasses;
        
        for C in E do 
            R := Representative(C);
            Aut := AutF(C);
            T0 := List(GeneratorsOfGroup(Aut), alpha -> List(GeneratorsOfGroup(R), x -> x^-1*Image(alpha,x)));
            T := ClosureGroup(T, Flat(T0));
        od;

        return T;
    end );

# InstallMethod(IsReduced, "for a saturated fusion system",
#     [IsSaturatedFusionSystemRep],
#     function(F)
#         return IsTrivial(Core(F)) and FocalSubgroup(F) = UnderlyingGroup(F);
#     end );

# Foc := function(S, L)
#     local T, A, X, T0;

#     T := TrivialSubgroup(S);
#     for A in L do 
#         X := Source(Identity(A));
#         T0 := List(GeneratorsOfGroup(A), alpha -> List(GeneratorsOfGroup(X), x -> x^-1*Image(alpha, x)));
#         T := ClosureGroup(T, Flat(T0));
#     od;

#     return T;
# end;

InstallMethod(IsSaturated, "for a saturated fusion system",
    [IsSaturatedFusionSystemRep],
    function(F)
        local S, C, L;

        L := CentricFClasses(F);
        L := Filtered(L, C -> IsCentric(C) and IsRadical(C));
        
        if ForAny(L, C -> Representative(C)=S or not C in F!.essclasses) then 
            return false;
        fi;

        return ForAll(L, IsSaturated);
    end );

