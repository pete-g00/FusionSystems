InstallMethod(Reps, "generic method",
    [IsFClassRep],
    function(C)
        return C!.R.class;
    end );

InstallMethod(Representative, "generic method",
    [IsFClassRep],
    function(C)
        return C!.A;
    end );

InstallMethod(ViewObj, "generic method",
    [IsFClass], 0,
    function(C)
        Print(Representative(C), "^F");
    end );

# G : the semidirect product S : Out_F(S)
# f : the inclusion map of S into G
# A : a subgroup of S
# L : list of Aut_F(E_i), up to Aut_F(S)-class
# d: dictionary of essential subgroups
InstallGlobalFunction(OrbitUpToClass, function(G, f, A, d)
    local   L, # Aut_F(S)-conjugates of A
            Acts, # the maps that conjugate A to another AutF_(S)-conjugate
            entries, # the entries in d
            L0, L00, # Aut_F(S)-conjugates of A whose Aut_F(E_i)-conjugates haven't been found
            X, # a F-conjugate of A
            i,j,k,l, # counters
            Subs, # the essential subgroups
            Maps, # maps between essential subgroups in different Aut_F-classes
            E, # essential subgroup
            C, # Aut_F(S)-conjugates of E containing X (and maps)
            B, # a single Aut_F(S)-conjugate of E containing X (and maps)
            B0,B1, # a single Aut_F(S)-conjugate of E containing X
            rf1, rf0, # restrictions of f
            x,y, # the element that conjugates an Aut_F(S)-conjugate of E
            a, # a map that conjugates between Aut_F(S)-reps of an essential subgroup F-conjugates
            alpha, # an automorphism of E that conjugates E to an Aut_F(S)-conjugate
            Auto, # the automizer of B1 in F
            O, # the Auto-orbit of B1 (up to B1-class)
            T; # the maps from A to an Aut_F(S)-conjugate

    L := [A]; 
    Acts := [IdentityMapping(A)];
    # L0 := [A];

    entries := d!.entries;
    k := 1;

    while k <= Length(L) do 
        Info(InfoFClass, 1, "Looking at index ", k);
        X := L[k];
        for i in [2..Length(entries)] do
            Subs := Reps(entries[i][1]);
            Maps := entries[i][1]!.R.maps;
            Auto := entries[i][2];
            for j in [1..Length(Subs)] do
                # all essubs, up to Aut-S class, to be considered
                E := Subs[j];
                C := ContainingConjugates(G, Image(f,E), Image(f,X));
                Info(InfoFClass, 1, "Have ", Length(C), " Aut_F(S)-conjugates of E containing A");
                # find all F-conjugates
                for B in C do 
                    B1 := PreImage(f, B[1]);
                    # maps E^f -> B1^f
                    x := B[2];
                    a := Maps[j];
                    B0 := Image(a);
                    y := RepresentativeAction(G,Image(f,B0),Image(f,E));
                    x := ConjugatorIsomorphism(Image(f,B0),y*x);

                    # E -> a(E) -> f(a(E)) -> f(a(E))^(yx) -> f^{-1}(f(a(E))^x)
                    rf1 := RestrictedHomomorphism(f,B0,Image(f,B0));
                    rf0 := RestrictedHomomorphism(RestrictedInverseGeneralMapping(f),Image(f,B1),B1);
                    alpha := a*rf1*x*rf0;
                    Assert(0, IsGroupHomomorphism(alpha));
                    Auto := OnAutGroupConjugation(Auto, alpha);
                    
                    # check which ones are not already Aut_F(S)-conjugate in E and append those
                    O := Orbit(Auto, X^B1, OnCoCl(B1));
                    O := Set(List(O, A -> Image(f,Representative(A))^G));
                    Info(InfoFClass, 1, "The Aut_F(E)-orbit has ", Length(O), " subgroups up to Aut_F(S)-class");
                    
                    O := List(O, A -> PreImage(f,Representative(A)));
                    O := Filtered(O, A -> ForAll(L, P -> not Image(f,A) in Image(f,P)^G));
                    Info(InfoFClass, 1, "of which ", Length(O), " are new");

                    Append(L, O);
                    
                    T := List(O, Y -> Acts[k]*RestrictedHomomorphism(RepresentativeAction(Auto, X, Y, OnImage),X,Y));
                    Append(Acts, T);
                od;
            od;
        od;
        k := k+1;
    od;

    return rec(
        class := L,
        maps := Acts
    );
end );

InstallMethod(FClass, "for a fusion system and a group",
    [IsFusionSystem, IsGroup],
    function(F, A)
        local R;

        R := OrbitUpToClass(F!.G, F!.f, A, F!.d);
        return FClass(F!.G, F!.f, A, R, F!.S);
    end);

InstallMethod(\^, "generic method",
    [IsGroup, IsFusionSystem],
    function(A,F)
        return FClass(F,A);
    end );

InstallOtherMethod(FClass, "for all data",
    [IsGroup, IsGroupHomomorphism, IsGroup, IsRecord, IsGroup],
    function(G,f,A,R,S)
        return Objectify(
            NewType(CollectionsFamily(FamilyObj(A)), IsFClassRep),
            rec(G := G, f := f, A := A, R := R, S := S));
    end );

InstallMethod(Size, "for a F-class",
    [IsFClassRep],
    function(C)
        local n, f, G, T;

        n := 0;
        f := C!.f;
        G := C!.G;

        for T in Reps(C) do 
            n := n + Size(Image(f,T)^G);
        od;

        return n;
    end );

InstallMethod(\in, "for a subgroup and F-class",
    [IsGroup, IsFClassRep],
    function(A, C)
        local f, G;

        f := C!.f;
        G := C!.G;

        return ForAny(Reps(C), T -> Image(f,A) in Image(f,T)^G);
    end );

InstallMethod(\<, "for F-classes",
    [IsFClassRep, IsFClassRep],
    function(C1, C2)
        return Representative(C1) < Representative(C2);
    end );

# find a way to iterate through the elements

InstallMethod(FindMap, "for a F-Class and a subgroup",
    [IsFClass, IsGroup],
    function(C, B)
        local   A, # the representative of C
                f, # the inclusion map S -> S : Out_F(S)
                Subs, # Aut_F(S)-reps of C
                Maps, # maps that conjugate between Aut_F(S)-reps
                G, # the semidirect product
                i, # a counter
                T, # an Aut_F(S)-reps of C
                x; # map from A to Aut_F(S)-rep

        A := C!.A;
        f := C!.f;
        Subs := Reps(C);
        Maps := C!.R.maps;
        G := C!.G;

        for i in [1..Length(Subs)] do 
            T := Subs[i];
            if Image(f,B) in Image(f,T)^G then 
                x := RepresentativeAction(G,Image(f,T),Image(f,B));
                x := ConjugatorIsomorphism(Image(f,T),x);
                x := OnHomConjugation(x, RestrictedInverseGeneralMapping(f));
                return Maps[i]*x;
            fi;
        od;

        return fail;
    end);

InstallMethod(AsSSortedList, "for a F-class",
    [IsFClassRep],
    function(C)
        local L, f, G, T;

        L := [];
        f := C!.f;
        G := C!.G;

        for T in Reps(C) do 
            Append(L, List(Image(f,T)^G, X -> PreImage(f,X)));
        od;

        return L;
    end );

InstallMethod(\=, "for two F-classes",
    [IsFClassRep, IsFClassRep],
    function (C1, C2)
        local L1, L2, f, G;

        if C1!.S <> C2!.S then 
            return false;
        fi;

        if Size(C1) <> Size(C2) then 
            return false;
        fi;

        if C1!.G <> C2!.G then 
            return Set(C1) = Set(C2);            
        fi;
        
        L1 := Reps(C1);
        L2 := Reps(C2);

        if Length(L1) <> Length(L2) then 
            return false;
        fi;

        f := C1!.f;
        G := C2!.G;

        L1 := List(L1, A -> Image(f,A)^G);
        L2 := List(L2, A -> Image(f,A)^G);

        return Set(L1) = Set(L2);
    end );

InstallMethod(IsCentric, "for a F-class",
    [IsFClassRep],
    function(C)
        local S;

        S := Source(C!.f);
        return ForAll(Reps(C), T -> Centralizer(S,T) = Center(T));
    end );

InstallMethod(IsSaturated, "for a fusion system and a F-class",
    [IsFusionSystem, IsFClassRep],
    function(F, C)
        local Subs, Maps, f, S, p, R, AutR, AutSR, T, CheckSaturated, i, B, AutSB;

        Subs := Reps(C);
        Maps := C!.R.maps;
        f := F!.f;
        S := Source(f);
        p := F!.p;
        
        R := Representative(C);
        AutR := AutF(F, R);
        AutSR := Automizer(S,R);
        T := RightTransversal(AutR, AutSR);

        CheckSaturated := function(i)
            local j, A, phi, alpha, N;

            for j in [1..Length(Subs)] do 
                A := Subs[j];
                for phi in T do 
                    alpha := InverseGeneralMapping(Maps[j])*phi*Maps[i];
                    Assert(0, IsGroupHomomorphism(alpha));

                    N := NPhi(S, alpha);
                    if N <> Source(alpha) and ExtendAut(alpha, AutF(F,N)) = fail then
                        return false;
                    fi;
                od;
            od;

            return true;
        end;

        for i in [1..Length(Subs)] do 
            B := Subs[i];
            AutSB := Index(Normalizer(Image(f,S),Image(f,B)), Centralizer(Image(f,S),Image(f,B)));

            # B is fully automized
            if Size(AutR)/AutSB mod p <> 0 then 
                if CheckSaturated(i) then 
                    return true;
                fi;
            fi;
        od;

        return false;
    end );
