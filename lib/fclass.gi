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
# d: dictionary of essential subgroups
InstallGlobalFunction(OrbitUpToClass, function(G, f, A, d)
    local   L, # Aut_F(S)-conjugates of A
            Acts, # the maps that conjugate A to another AutF_(S)-conjugate
            entries, # the entries in d
            X,Y,Y0, # a F-conjugate of A
            CL, # a F-class of essential subgroup
            L0, # Aut_F(S)-reps of X up to E-class
            A0, # Aut_F(S)-reps of X up to E-class (containing X)
            i,j, # counters
            C, # Aut_F(S)-conjugates of E containing X (and maps)
            B, # a single Aut_F(S)-conjugate of E containing X (and maps)
            B1, # a single Aut_F(S)-conjugate of E containing X
            x,a,b, # the element that conjugates a F-conjugate of E
            Auto, # the automizer of B1 in F
            O, # the Auto-orbit of B1 (up to B1-class)
            T; # the maps from A to an Aut_F(S)-conjugate

    L := [A]; 
    Acts := [IdentityMapping(A)];

    entries := d!.entries;
    j := 1;

    while j <= Length(L) do 
        Info(InfoFClass, 1, "Looking at index ", j);
        X := L[j];
        for i in [2..Length(entries)] do
            CL := entries[i][1];
            C := ContainingFConjugates(CL, X);
            Info(InfoFClass, 2, "Have ", Length(C), " F-conjugate(s) of E containing A, up to Aut_F(S)-class");
            # find all F-conjugates
            for B in C do 
                Auto := entries[i][2];
                B1 := B[1];
                L0 := DescendReps(Image(f,X), Image(f,B1), Image(f));
                L0 := List(L0, A -> PreImage(f,A));
                Info(InfoFClass, 2, "There are ", Length(L0), " Aut_F(S)-reps");
                A0 := [];
                for Y in L0 do 
                    if IsSubset(B1,Y) then 
                        Add(A0, Y);
                    elif ForAll(L, A -> not Image(f,X) in Image(f,A)^G) then
                        Add(L, Y);
                        a := RepresentativeAction(B1, X, Y, OnImage);
                        Info(InfoFClass, 2, [Source(Acts[j]), X,Y]);
                        Add(Acts, Acts[j]*ConjugatorIsomorphism(X, RepresentativeAction(B1, X, Y)));
                    fi;
                od;
                Info(InfoFClass, 2, "of which ", Length(A0), " contain Y");
                
                x := B[2];
                Auto := OnAutGroupConjugation(Auto, x);
                
                # check which ones are not already Aut_F(S)-conjugate in E and append those
                O := Flat(Orbits(Auto, A0, OnImage));
                Info(InfoFClass, 2, "The Aut_F(E)-orbit has ", Length(O), " subgroups up to Aut(E)-class");
                
                # O := List(O, A -> PreImage(f,Representative(A)));
                # O := Filtered(O, A -> ForAll(L, P -> not Image(f,A) in Image(f,P)^G));

                # Y is Aut(E)-conjugate to Aut_F(S)-conjugate of X
                for Y in O do 
                    if ForAll(L, P -> not Image(f,Y) in Image(f,P)^G) then 
                        Add(L, Y);
                        Y0 := First(A0, X -> RepresentativeAction(Auto, X, Y, OnImage) <> fail);
                        a := RepresentativeAction(Auto, Y0, Y, OnImage);
                        Assert(0, a <> fail);
                        b := RepresentativeAction(G, Image(f,X), Image(f,Y0));
                        Assert(0, b <> fail);
                        b := OnHomConjugation(ConjugatorIsomorphism(Image(f,X), b), RestrictedInverseGeneralMapping(f));
                        Add(Acts, Acts[j]*b*RestrictedHomomorphism(a, Y0, Y));
                    fi;
                od;
                Info(InfoFClass, 2, "Have ", Length(L), " classes now");

                # Append(L, O);
                
                # T := List(O, Y -> Acts[j]*RestrictedHomomorphism(RepresentativeAction(Auto, X, Y, OnImage),X,Y));
                # Append(Acts, T);
            od;
        od;
        j := j+1;
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
        local B, f, G;

        B := Representative(C);
        if IsomType(A) <> IsomType(B) then 
            return false;
        fi;

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

InstallMethod(Enumerator, "for a F-class", [IsFClassRep], AsSSortedList);

InstallMethod(ContainingFConjugates, "generic method",
    [IsFClassRep, IsGroup],
    function(C, A)
        local Subs, Maps, f, G, L, i, Co, T, X, A1, x;
    
        Subs := Reps(C);
        Maps := C!.R.maps;
        f := C!.f;
        G := C!.G;
        L := [];

        for i in [1..Length(Subs)] do 
            T := Subs[i];
            Co := ContainingConjugates(G, Image(f,T), Image(f,A));
            for X in Co do 
                A1 := PreImage(f,X[1]);
                x := ConjugatorIsomorphism(Image(f,T), X[2]);
                x := OnHomConjugation(x, RestrictedInverseGeneralMapping(f));;
                Add(L, [A1, Maps[i]*x]);
            od;
        od;

        return L;
    end );

InstallMethod(ContainedFConjugates, "generic method",
    [IsFClassRep, IsGroup],
    function(C, A)
        local Subs, Maps, f, G, L, i, Co, T, X, A1, x, mi;
    
        Subs := Reps(C);
        Maps := C!.R.maps;
        f := C!.f;
        G := C!.G;
        L := [];

        for i in [1..Length(Subs)] do 
            T := Subs[i];
            # returns [A^x, x] such that A^x \leq T
            Co := ContainedConjugates(G, Image(f,T), Image(f,A));
            for X in Co do 
                A1 := PreImage(f,X[1]);
                x := ConjugatorIsomorphism(Image(f,A), X[2]);
                x := OnHomConjugation(x, RestrictedInverseGeneralMapping(f));;
                Add(L, [A1, x]);
            od;
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
            AutSB := IndexNC(Normalizer(Image(f,S),Image(f,B)), Centralizer(Image(f,S),Image(f,B)));

            # B is fully automized
            if Size(AutF(F,B))/AutSB mod p <> 0 then 
                if CheckSaturated(i) then 
                    return true;
                fi;
            fi;
        od;

        return false;
    end );

# InstallMethod(IsSaturated, "for a fusion system and a F-class, given AutF",
#     [IsFusionSystem, IsFClassRep, IsGroupOfAutomorphisms],
#     function(F, C, AutR)
#         local Subs, Maps, f, S, p, R, AutSR, T, CheckSaturated, i, B, AutSB;

#         Subs := Reps(C);
#         Maps := C!.R.maps;
#         f := F!.f;
#         S := Source(f);
#         p := F!.p;
        
#         R := Representative(C);
#         AutSR := Automizer(S,R);
#         T := RightTransversal(AutR, AutSR);

#         CheckSaturated := function(i)
#             local j, A, phi, alpha, N;

#             for j in [1..Length(Subs)] do 
#                 A := Subs[j];
#                 for phi in T do 
#                     alpha := InverseGeneralMapping(Maps[j])*phi*Maps[i];
#                     Assert(0, IsGroupHomomorphism(alpha));

#                     N := NPhi(S, alpha);
#                     if N <> Source(alpha) and ExtendAut(alpha, AutF(F,N)) = fail then
#                         return false;
#                     fi;
#                 od;
#             od;

#             return true;
#         end;

#         for i in [1..Length(Subs)] do 
#             B := Subs[i];
#             AutSB := IndexNC(Normalizer(Image(f,S),Image(f,B)), Centralizer(Image(f,S),Image(f,B)));

#             # B is fully automized
#             if Size(AutF(F,B))/AutSB mod p <> 0 then 
#                 if CheckSaturated(i) then 
#                     return true;
#                 fi;
#             fi;
#         od;

#         return false;
#     end );

