# Currently working on the $\calF = \calF_S(G)$ case

EssentialSubgroups := function(S, G)
    local f, p, L;

    p := PrimePGroup(S);
    f := IsomorphismPcGroup(S);
    S := Image(f);

    L := AllProtoEssentials(S);
    L := List(L, A -> PreImage(f, A));

    # TODO: Up to $G$-conjugacy
    return Filtered(L, A -> PCore(Normalizer(G,A), p) = A);
end;

AutFA := function(S, G, A)
    return Automizer(G, A);
end;

IsFullyNormalized := function(S, G, A)
    local p, NSA, NGA;

    p := PrimePGroup(S);

    NSA := Normalizer(S, A);
    NGA := Normalizer(G, A);

    return IndexNC(NGA, NSA) mod p <> 0;
end;

IsFullyCemtralized := function(S, G, A)
    local p, CSA, CGA;

    p := PrimePGroup(S);

    CSA := Centralizer(S, A);
    CGA := Centralizer(G, A);

    return IndexNC(CGA, CSA) mod p <> 0;
end;

IsFullyAutomized := function(S, G, A)
    local p, AutSA, AutGA;

    p := PrimePGroup(S);

    AutSA := Automizer(S, A);
    AutGA := Automizer(G, A);

    return IndexNC(AutSA, AutGA) mod p <> 0;
end;

LoadPackage("datastructures");

DFS_OrbitStabilizer_fs := function(L, S, A)
    local   O,      # the orbit of $A$
            T,      # how can we map $A -> O[i]$
            Q,      # the queue
            Stab,   # stabilizer set
            X,      # the element popped from the queue
            i,      # position of X in O
            phi,    # a generator of $F$
            Y,      # the conjugate $X \phi$
            j,      # position of Y in O (if any) up to S-conjugacy
            a,      # the element in S that conjugates Y to O[j]
            s;      # an element that stabilizes A

    O := [A];
    T := [IdentityMapping(A)];
    Q := Stack();
    Push(Q, A);

    Stab := Group(IdentityMapping(A));

    while Size(Q) <> 0 do 
        X := Pop(Q);
        i := Position(O, X);
        for phi in L do 
            if IsSubset(Source(phi), X) then 
                Y := Image(phi, X);
                j := PositionProperty(O, Z -> IsConjugate(S, Y, Z));
                if j = fail then 
                    Add(O, Y);
                    Push(Q, Y);
                    Add(T, T[i]*RestrictedMapping(phi, X));
                else 
                    Info(InfoWarning, 1, j);
                    a := RepresentativeAction(S, Y, O[j]);
                    s := T[i] * RestrictedMapping(phi, X) * ConjugatorIsomorphism(Y, a) * InverseGeneralMapping(T[j]);
                    Info(InfoWarning, 1, [
                        T[i], RestrictedMapping(phi, X), ConjugatorIsomorphism(Y, a), InverseGeneralMapping(T[j])
                    ]);
                    Stab := ClosureGroup(Group(s), Stab);
                fi;
            fi;
        od;
    od;

    return rec(
        O := O,
        T := T,
        Stab := Stab
    );
end;
