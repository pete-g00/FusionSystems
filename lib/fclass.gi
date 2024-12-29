InstallGlobalFunction(AutomizerClass, function(A, S, d)
    local   InitializeClass,
            DoMarkFound,
            MarkFound,
            FirstFalse,
            L,
            Aut,
            f, i,
            A0,
            E0,
            Auto,
            a,
            E,
            n,
            O,
            St,
            StA0,
            StA,
            T,
            m;
    
    L := [];
    
    InitializeClass := function(A0, m)
        local X, BL, maps, NSA, i, E, D, L0, g;

        Info(InfoFClass, 2, "Initializing new F-conjugate");
        X := [];
        BL := [];
        NSA := Normalizer(S,A0);

        for i in [1..Length(d)] do 
            Info(InfoFClass, 3, " with respect to essub ", i);
            E := Representative(d[i]);
            D := ContainedConjugates(S, E, A0, true);
            if D = fail then
                L0 := [];
            else 
                # only need a N_S(A)-representative of [A,E^a] for a in S
                # to get every possible automizer gain
                g := D[2];
                # A0^g \leq E => A0 \leq E^(g^-1)
                D := E^(g^-1);
                D := DescendReps(D, S, NSA);
                D := Filtered(D, B -> IsSubset(B, A0));
                L0 := D;
            fi;
            Info(InfoFClass, 3, "  found ", Length(L0), " inclusion(s) up to normalizer class");
            Add(X, L0);
            Add(BL, BlistList([1..Length(L0)], []));
        od;

        Add(L, rec(A := A0, L := X, BL := BL, m := m));
    end;

    DoMarkFound := function(A0, E0, i, j)
        local L0, D, NSA, k;

        L0 := L[i];
        D := ContainedConjugates(S, E0, L0.A, true);
        D := E0^(D[2]^-1);
        NSA := Normalizer(S, L0.A);
        k := PositionProperty(L0.L[j], X -> RepresentativeAction(NSA, X, D) <> fail);
        Assert(0, k <> fail and not L0.BL[j][k]);
        L0.BL[j][k] := true;
    end;

    MarkFound := function(A0, E0, j)
        local i;

        for i in [1..Length(L)] do 
            if RepresentativeAction(S, L[i].A, A0) <> fail then
                DoMarkFound(A0, E0, i, j);
                return i;
            fi;
        od;

        return fail;
    end;
    
    FirstFalse := function()
        local i,j,k;

        for i in [1..Length(L)] do
            for j in [1..Length(L[i].BL)] do 
                k := Position(L[i].BL[j], false);
                if k <> fail then 
                    return rec(i := i, j := j, k := k); 
                fi;
            od;
        od;

        return fail;
    end;

    Aut := Automizer(S, A);
    InitializeClass(A, IdentityMapping(A));
    f := FirstFalse();

    while f <> fail do
        Info(InfoFClass, 2, "Looking at ", [f.i,f.j,f.k]);

        A0 := L[f.i].A;
        E := L[f.i].L[f.j][f.k];
        Auto := AutF(d[f.j]);
        a := FindMap(d[f.j], E);

        Auto := OnAutGroupConjugation(Auto, a);
        n := NiceMonomorphism(Auto);

        O := Orbit(Image(n, Auto), A0^E, OnCoClNM(E, n));
        O := List(O, Representative);
        Info(InfoFClass, 3, "Orbit of length ", Length(O), " up to E-class");
        O := AscendReps(O, S, E);
        Info(InfoFClass, 3, " and ", Length(O), " up to S-class");

        for T in O do
            i := MarkFound(T, E, f.j); 
            if i = fail then
                Info(InfoFClass, 3, "New Aut_F(S)-conjugate found");
                m := RepresentativeAction(Image(n, Auto), A0, T, OnImageNM(n));
                m := PreImagesRepresentative(n, m);
                m := RestrictedHomomorphismNC(m, A0, T);
                InitializeClass(T, L[f.i].m * m);
                DoMarkFound(T, E, Length(L), f.j);
            else 
                Info(InfoFClass, 3, "Found Aut_F(S)-conjugate at index ", i);
            fi;
        od;

        St := Stabilizer(Image(n, Auto), A0, OnImageNM(n));
        if not IsTrivial(St) then 
            StA0 := Group(List(GeneratorsOfGroup(St), a -> RestrictedHomomorphismNC(PreImagesRepresentative(n, a), A0, A0)));
            StA := OnAutGroupConjugation(StA0, InverseGeneralMapping(L[f.i].m));
            Aut := ClosureGroup(Aut, StA);
        fi;

        f := FirstFalse();
    od;
    
    return rec(
        class := List(L, c -> rec(sub := c.A, map := c.m)), 
        autf := Aut
    );
end );

InstallMethod(FClass, "for a fusion system and a group",
    [IsFusionSystem, IsGroup],
    function(F, A)
        local L, i, R, C;

        # check if FClass has already been found
        L := F!.knownclasses;
        i := PositionSortedBy(L, Size(A), T -> Size(Representative(T)));
        while i <= Length(L) and Size(A) = Size(Representative(L[i])) do 
            if A in L[i] then return L[i]; fi;
            i := i+1;
        od;

        # if not, then construct the class
        R := AutomizerClass(A, UnderlyingGroup(F), F!.essclasses);
        C := Objectify(NewType(CollectionsFamily(FamilyObj(A)), IsFClassRep),
            rec(data := R.class));

        SetRepresentative(C, A);
        SetAutF(C, R.autf);
        SetUnderlyingFusionSystem(C, F);
        AddSet(L, C);

        return C;
    end);

InstallOtherMethod(\^, "generic method",
    [IsGroup, IsFusionSystem],
    function(A,F)
        return FClass(F,A);
    end );

InstallOtherMethod(ViewObj, "generic method",
    [IsFClass], 0,
    function(C)
        Print(Representative(C), "^F");
    end );

InstallOtherMethod(Size, "for a F-class",
    [IsFClassRep],
    function(C)
        local S;

        S := UnderlyingGroup(UnderlyingFusionSystem(C));
        return Sum(List(C!.data, T -> Size(T.sub^S)));
    end );

InstallOtherMethod(\in, "for a subgroup and F-class",
    [IsGroup, IsFClassRep],
    function(A, C)
        local B, S;

        B := Representative(C);
        if IsomType(A) <> IsomType(B) then 
            return false;
        fi;

        S := UnderlyingGroup(UnderlyingFusionSystem(C));
        return ForAny(C!.data, T -> RepresentativeAction(S, A, T.sub) <> fail);
    end );

InstallMethod(\<, "for F-classes",
    [IsFClassRep, IsFClassRep],
    function(C1, C2)
        local S;

        S := UnderlyingGroup(UnderlyingFusionSystem(C1));
        if C1 = C2 then 
            return false;
        elif Size(Representative(C1)) < Size(Representative(C2)) then 
            return true;
        fi;

        return Representative(C1) < Representative(C2);
    end );

# find a map from A=Representative(D) to B in F
InstallMethod(FindMap, "for a F-Class and a subgroup",
    [IsFClassRep, IsGroup],
    function(C, B)
        local   S,  # attributes of C
                T,  # an Aut_F(S)-rep of C
                x,  # S-conjugator to B
                b;  # S-conjugation map

        S := UnderlyingGroup(UnderlyingFusionSystem(C));

        for T in C!.data do 
            x := RepresentativeAction(S, T.sub, B);
            if x <> fail then 
                b := ConjugatorIsomorphism(T.sub, x);
                return  T.map*b;
            fi;
        od;

        return fail;
    end);

InstallOtherMethod(Automizer, "for a specific subgroup",
    [IsFClassRep, IsGroup],
    function(C, A)
        local x;

        x := FindMap(C, A);
        if x = fail then 
            Error("A does not lie in A");
        fi;

        return OnAutGroupConjugation(AutF(C), x);
    end );

InstallOtherMethod(AsSSortedList, "for a F-class",
    [IsFClassRep],
    function(C)
        local S, Subs, L;

        S := UnderlyingGroup(UnderlyingFusionSystem(C));
        L := Flat(List(C!.data, T -> AsList(T.sub^S)));

        return Immutable(L);
    end );

InstallOtherMethod(Enumerator, "for a F-class", [IsFClassRep], AsList);

InstallOtherMethod(\=, "for two F-classes",
    [IsFClassRep, IsFClassRep],
    function (C1, C2)
        local L1, L2, S;
        
        S := UnderlyingGroup(UnderlyingFusionSystem(C1));

        if not (IsIdenticalObj(S, UnderlyingGroup(UnderlyingFusionSystem(C2))) and Size(C1) = Size(C2)) then 
            return false;
        fi; 

        if Size(C1) < 500 or not IsIdenticalObj(UnderlyingFusionSystem(C1), UnderlyingFusionSystem(C2)) then 
            return Set(Elements(C1)) = Set(Elements(C2));
        fi;
        
        L1 := C1!.data;
        L2 := C2!.data;

        if Length(L1) <> Length(L2) then 
            return false;
        fi;
        
        return ForAll(L1, r -> r.sub in C2);
    end );

InstallMethod(IsCentric, "for a F-class",
    [IsFClassRep],
    function(C)
        local S;

        S := UnderlyingGroup(UnderlyingFusionSystem(C));
        return ForAll(C!.data, T -> Centralizer(S,T.sub) = Center(T.sub));
    end );

InstallMethod(IsRadical, "generic method",
    [IsFClassRep],
    function(C)
        local A, S, p, AutFC, ASA, n, InnA;

        A := Representative(C);
        S := UnderlyingGroup(UnderlyingFusionSystem(C));
        p := Prime(UnderlyingFusionSystem(C));
        AutFC := AutF(C);
        ASA := Automizer(S, A);
        InnA := Automizer(A, A);

        if not HasNiceMonomorphism(AutFC) then 
            AssignNiceMonomorphismAutomorphismGroup(AutFC);
        fi;
        n := NiceMonomorphism(AutFC);

        return Intersection(Image(n, PCore(AutFC, p)), Image(n,ASA)) = Image(n, InnA);
    end );

InstallMethod(IsSaturated, "for a fusion system and a F-class, given AutF",
    [IsFClassRep],
    function(C)
        local CheckFullyAutomized, CheckReceptive, F, p, S, i;
        
        F := UnderlyingFusionSystem(C);
        p := Prime(F);
        S := UnderlyingGroup(F);

        CheckFullyAutomized := function(i)
            local AutSR;

            AutSR := IndexNC(Normalizer(S, C!.data[i].sub), Centralizer(S, C!.data[i].sub));
            return Size(AutF(C))/AutSR mod p <> 0;
        end;

        CheckReceptive := function(i)
            local R1, AutFR, AutSR, n, T, m1, m2, R2, phi, alpha, N, j;
            
            R1 := C!.data[i];

            AutFR := Automizer(C, R1.sub);
            AutSR := Automizer(S, R1.sub);
            
            if not HasNiceMonomorphism(AutFR) then 
                AssignNiceMonomorphismAutomorphismGroup(AutFR);
            fi;

            n := NiceMonomorphism(AutFR);
            T := RightTransversal(Image(n,AutFR), Image(n,AutSR));
            m1 := FindMap(C, R1.sub);
            
            for R2 in C!.data do 
                Info(InfoFClass, 4, " Checking next representative");
                m2 := FindMap(C, R2.sub);
                for j in [2..Length(T)] do
                    Info(InfoFClass, 4, "  looking at map ", j);
                    alpha := T[j];
                    phi := InverseGeneralMapping(R2.map)*R1.map*PreImagesRepresentative(n,alpha);
                    Assert(0, IsGroupHomomorphism(phi));
                    N := NPhi(S, phi);
                    if N <> Source(phi) and ExtendAut(phi, Automizer(F,N)) = fail then
                        Info(InfoFClass, 5, "  which doesn't extend to N_phi");
                        return false;
                    else 
                        Info(InfoFClass, 5, "  which does extend to N_phi");
                    fi;
                od;
            od;

            return true;
        end;

        for i in [1..Length(C!.data)] do 
            Info(InfoFClass, 3, "Checking IsSaturated condition for ", i, "-th representative");
            if CheckFullyAutomized(i) then 
                Info(InfoFClass, 3, "Is fully automized");
                if CheckReceptive(i) then 
                    Info(InfoFClass, 3, "Is receptive");
                    return true;
                fi;
            fi;
        od;
    end );
