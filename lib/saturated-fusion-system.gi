InfoFusion := NewInfoClass("InfoFusion");
SetInfoLevel(InfoFusion, 1);

# G : the semidirect product S : Out_F(S)
# f : the inclusion map of S into G
# A : a subgroup of S
# L : list of Aut_F(E_i), up to Aut_F(S)-class
# d: dictionary of essential subgroups
OrbitUpToClass := function(G, f, A, d)
    local   L, # Aut_F(S)-conjugates of A
            Acts, # the maps that conjugate A to another AutF_(S)-conjugate
            entries, # the entries in d
            L0, L00, # Aut_F(S)-conjugates of A whose Aut_F(E_i)-conjugates haven't been found
            X, # a F-conjugate of A
            i,j,k,l, # counters
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
        Info(InfoFusion, 1, "Looking at index ", k);
        X := L[k];
        for i in [1..Length(entries)] do
            Subs := Reps(entries[i][1]);
            Maps := entries[i][1].maps;
            Auto := entries[i][2];
            for j in [1..Length(Subs)] do
                # all essubs, up to Aut-S class, to be considered
                E := Subs[j];
                C := ContainingConjugates(G, Image(f,E), Image(f,X));
                Info(InfoFusion, 1, "Have ", Length(C), " Aut_F(S)-conjugates of E containing A");
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
                    Info(InfoFusion, 1, "The Aut_F(E)-orbit has ", Length(O), " subgroups up to Aut_F(S)-class");
                    
                    O := List(O, A -> PreImage(f,Representative(A)));
                    O := Filtered(O, A -> ForAll(L, P -> not Image(f,A) in Image(f,P)^G));
                    Info(InfoFusion, 1, "of which ", Length(O), " are new");

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
end;

# automizer in a similar manner
SaturatedFusionSystem := function(S, L)
    p := FindPrimeOfPrimePower(Size(S));
    SGens := Filtered(L, x -> Source(x) = S);
    AutFS := ClosureGroup(InnerAutomorphismGroup(S), SGens);

    if not IsSolvable(AutFS) then 
        Error("Aut_F(S) is not solvable.");
    fi;

    B := SylowComplement(AutFS, p);
    G := SemidirectProduct(B, S);
    f := Embedding(G,2);

    L := Filtered(L, x -> Source(x) <> S);
    if IsEmpty(L) then 
        return rec(
            S := S,
            G := G,
            f := f
        );
    fi;
    
    # we sort to capture ALL the containment relations between the essential subgroups
    SortBy(L, x -> Size(Source(x)));

    d := NewDictionary(S, true);
    E := [];
    while not IsEmpty(L) do 
        X := Source(L[1]);
        R := OrbitUpToClass(G, f, X, E{[2..Length(E)]}, d);
        C := FClassCons(G, f, X, R);
        
        I := Filtered([1..Length(L)], i -> Source(L[i]) in C);
        cmaps := List(I, i -> FindMap(C, Source(L[i])));
        # conjugate hom[i] with ms[i]
        # construct the closure of Aut_F(S)
        # add it to the dictionary d
        L0 := List([1..Length(I)], i -> OnHomConjugation(L[I[i]], cmaps[i]));
        AutFX := Group(L0);
        AddDictionary(C, AutFX);

        L := L{Difference([1..Length(L)], I)};
    od;

    return rec(
        S := S,
        G := G,
        f := f
    );
end;

AutF := function(F, A)
    # find all essubs containing A
    # find automizer using Aut_F(E_i)
end;

RepresentativeFIsomorphism := function(F, A, B)

end;

FClass := function(F, A)

end;

FClasses := function(F)

end;

IsSaturated := function(F)
    # find centric subs
    # check every Aut_F(A)-class is saturated
end;
