CSThru := function(G,normals)
    local cs,i,j,pre,post,c,new,rev;
    cs:=CompositionSeries(G);
    # find normal subgroups not yet in
    normals:=Filtered(normals,x->not x in cs);
    # do we satisfy by sheer dumb luck?
    if Length(normals)=0 then return cs;fi;

    SortBy(normals,x->-Size(x));
    # check that this is a valid series
    Assert(0,ForAll([2..Length(normals)],i->IsSubset(normals[i-1],normals[i])));

    # Now move series through normals by closure/intersection
    for j in normals do
        # first in cs that does not contain j
        pre:=PositionProperty(cs,x->not IsSubset(x,j));
        # first contained in j.
        post:=PositionProperty(cs,x->Size(j)>=Size(x) and IsSubset(j,x));

        # if j is in the series, then pre>post. pre=post impossible
        if pre<post then
        # so from pre to post-1 needs to be changed
        new:=cs{[1..pre-1]};

        rev:=[j];
        i:=post-1;
        repeat
            if not IsSubset(Last(rev),cs[i]) then
            c:=ClosureGroup(cs[i],j);
            if Size(c)>Size(Last(rev)) then
                # proper down step
                Add(rev,c);
            fi;
            fi;
            i:=i-1;
            # at some point this must reach j, then no further step needed
        until Size(c)=Size(cs[pre-1]) or i<pre;
        Append(new,Filtered(Reversed(rev),x->Size(x)<Size(cs[pre-1])));

        i:=pre;
        repeat
            if not IsSubset(cs[i],Last(new)) then
            c:=Intersection(cs[i],j);
            if Size(c)<Size(Last(new)) then
                # proper down step
                Add(new,c);
            fi;
            fi;
            i:=i+1;
        until Size(c)=Size(cs[post]);

        # change cs only if pre<post
        cs:=Concatenation(new,cs{[post+1..Length(cs)]});
        fi;
    od;
    return cs;
end;

FrattiniTest := function(S, P)
    local ucs, FP, Theta, g;

    ucs := Reversed(UpperCentralSeries(P));
    FP := FrattiniSubgroup(P);
    for Theta in ucs{[1..Minimum(2,Length(ucs))]} do 
        for g in RightTransversal(Normalizer(S,P),P) do
            if g in P then 
                continue; 
            fi;
            if IsSubgroup(ClosureGroup(Theta,FP), CommutatorSubgroup(Group(g),P))
                    and IsSubgroup(FP, CommutatorSubgroup(Group(g), Theta)) then
                return false;
            fi;
        od;   
    od;
    return true;
end;

LargeRankTest := function(S,P)
    local FP,NSP,k,l,s,sP;

    FP := FrattiniSubgroup(P);
    NSP := Normalizer(S,P); 

    k := PValuation(IndexNC(NSP, P), 2);
    l := Rank(P);

    if k >= 2 then
        # Note [s,P/Phi(P)] = [s,P]Phi(P)/Phi(P), and we can check the
        # inequality for s in a transversal to P in N_S(P), because for
        # each s in P, we have [s,Phi(P)] \leq Phi(P). 
        for s in RightTransversal(NSP,P) do
            if s in P then continue; fi;
            sP := CommutatorSubgroup(Group(s),P); 
            # Since [s,P]Phi(P)/Phi(P) is elementary abelian, to require
            # its rank \geq 2 is the same as requiring its order \geq 4. 
            if IndexNC(sP, Intersection(sP,FP)) < 4 then
                return false;
            fi;
        od;
    fi;

    return true;
end;

InstallMethod(PE_FAST2, "method to check whether E is proto-essential in S (fast)", 
    [IsPGroup, IsPGroup], function(S, E)
    local N, OutSE, i, A;

    N := Normalizer(S, E);
    # Out_S(E) must be: cyclic (order 2,4,8), quaternion (order 8) or eab (order 4, 8)
    if Index(N, E) > 8 then 
        Info(InfoFusion, 2, "\t(iii) \\Out_S(E) has order > 8");
        return false;
    elif Index(N, E) = 8 and IdGroup(N/E)[2] in [2,3] then 
        Info(InfoFusion, 2, "\t(iii) \\Out_S(E) invalid of order 8");
        return false;
    fi;

    if Size(E) <= 2^8 then 
        N := Normalizer(S, E);
        OutSE := N/E;
        i := IdGroup(OutSE);
        if not IdGroup(E) in ValidChoices!.(i[1])!.(i[2]) then 
            Info(InfoFusion, 2, "\t(iv) E invalid for given \\Out_S(E)");
            return false;
        fi;
    fi;
    
    if not FrattiniTest(S, E) then 
        Info(InfoFusion, 2, "\t(v) Failed Frattini Test");
        return false;
    elif not LargeRankTest(S, E) then 
        Info(InfoFusion, 2, "\t(vi) Failed rank test");
        return false;
    fi;

    # order 2^9: only look at init aut-grp - check Syl-2 is not normal here
    A := InitAutomorphismGroupOver(E);
    # if A is a 2-group, then Aut(E) is also a 2-group
    if A.size = 1 or (IsPrimePowerInt(A.size) and SmallestRootInt(A.size) = 2) then
        Info(InfoFusion, 2, "\t(vii) Aut_0(E) 2-group");
        return false;
    fi;

    return true;
end);

PcSubAutPGroup := function(AutPC, A)
    local L;

    L := List(GeneratorsOfGroup(A), x -> ImageAutPGroup(AutPC!.autrec, AutPC, x));
    return Subgroup(AutPC, L);
end;

InstallMethod(PE_SLOW2, "method to check whether E is proto-essential in S (slow)", 
    [IsPGroup, IsPGroup], function(S, E)
    local AutE, OutSE, AutSE, AutE_c, InnE, OutE, Aut2, N, C, n, q, A;

    AutE := AutomorphismGroupPGroup(E);
    OutSE := Normalizer(S,E)/E;
    
    if IsPrimePowerInt(AutE.size) then 
        Info(InfoFusion, 2, "\t(viii) Aut(E) is a 2-group");
        return false;
    fi;

    AutSE := Automizer(S, E);

    if AutE.glOrder = 1 then 
        Info(InfoFusion, 3, "\tAut(E) is solvable");

        AutE_c := ConvertHybridAutGroup(AutE);
        SetAutomorphismGroup(E, AutE_c);
        SetIsGroupOfAutomorphismsFiniteGroup(AutE_c, true);
        AutE := PcGroupAutPGroup(AutE);
        InnE := InnerAutGroupPGroup(AutE);
        AutSE := PcSubAutPGroup(AutE, AutSE);
    else 
        Info(InfoFusion, 3, "\tAut(E) is not solvable");
        AutE := ConvertHybridAutGroup(AutE);
        
        if not IsAbelian(E) then 
            InnE := InnerAutomorphismGroup(E);
        else 
            InnE := TrivialSubgroup(AutE);
        fi;

        SetIsGroupOfAutomorphismsFiniteGroup(AutE, true);
        n := NiceMonomorphism(AutE);
        SetAutomorphismGroup(E, AutE);
        SetNiceMonomorphism(AutE, n);

        AutE := Image(n, AutE);
        InnE := Image(n, InnE);
        AutSE := Image(n, AutSE);
    fi;

    if Size(OutSE) > 2 and IsElementaryAbelian(OutSE) then 
        N := Normalizer(AutE, AutSE);
        if Size(N) mod (Size(OutSE)-1) <> 0 then 
            Info(InfoFusion, 2, "\t(ix) N_{\\Out(E)}(\\Out_S(E)) does not have an element permuting the involutions transitively");
            return false;
        fi;
    fi;

    # radical test
    Aut2 := PCore(AutE, 2);
    if Size(Intersection(Aut2, AutSE)) <> IndexNC(E, Center(E)) then
        Info(InfoFusion, 2, "\t(x) E is not S-radical");
        return false;
    fi;

    # involution conjugate test
    q := NaturalHomomorphismByNormalSubgroupNC(AutE, InnE);
    OutE := Image(q);
    OutSE := Image(q, AutSE);

    if Size(OutSE) > 2 and IsElementaryAbelian(OutSE) then 
        N := Normalizer(OutE, OutSE);
        C := Centralizer(OutE, OutSE);
        if IndexNC(N, C) mod (Size(OutSE)-1) <> 0 then 
            Info(InfoFusion, 2, "\t(xi) N_{\\Out(E)}(\\Out_S(E)) does not have an element permuting the involutions transitively");
            return false;
        fi;
        # lift check -- the element of order 2^a - 1 must lift to N_S(E)
        N := Normalizer(S, E);
        A := AutomorphismGroup(N);
        if Size(A) mod (Size(OutSE)-1) <> 0 then 
            Info(InfoFusion, 3, "\t(xi) The map permuting involutions transitively cannot lift to N_S(E)");
            return false;
        fi;
    fi;

    return true;
end);

InstallMethod(GenerateProtoEssentials, "method to generate proto-essentials using the main proto-essentials", 
    [IsPGroup, IsList], function(S, L)
    local   G, # holomorph of S
            i, # Embedding of S to G
            S0, # Image of S in G
            I, # the conjugates of essentials already considered
            J, # the conjugates of essentials that still need to be considered
            L0, # the conjugates of essentials
            j, # position of the current essential
            E, # current essential
            T, # the proto-essentials
            N, # the normal subgroups of S
            A0, # the conjugates of E
            A0F, # the current conjugates of E
            A, # the larger proto-essentials containing E
            F, # an element in A
            E0, # some Aut(S)-conjugate of E contained inside F
            AutF, # Aut(F)
            n; # nice monomorphism for Aut(F)
    
    if IsEmpty(L) then 
        return L;
    fi;

    Info(InfoFusion, 1, "Generating all proto-essential subgroups");
        
    I := [];
    L0 := ShallowCopy(L);
    T := [];

    while Length(I) <> Length(L0) do 
        # we're dealing with some subgroup of largest order not yet considered
        J := Difference([1..Length(L0)], I);
        j := PositionMaximum(List(L0{J}, Size));
        j := J[j];
        E := L0[j];
        Add(I, j);
        Info(InfoFusion, 2, "Looking at position ", j);

        A0 := [E]; 
        A := List(T, X -> ContainedConjugates(S, X, E, true));
        A := Filtered(A, X -> X <> fail);
        Info(InfoFusion, 3, "\t", Length(A), " valid conjugate(s) of overgroup essentials");

        for F in A do
            E0 := E^(F[2]);

            AutF := AutomorphismGroup(F[1]);
            n := NiceMonomorphism(AutF);
            AutF := NiceObject(AutF);
            
            # Find Aut(F)-conjugates of subgroups in A0 that are not already present (up to Aut(S)-conjugacy)
            Info(InfoFusion, 3, "\t", "Finding Aut(F)-orbit of E");
            A0F := Orbit(AutF, E0, OnImageNM(n));
            Info(InfoFusion, 3, "\t", "Found");
            Info(InfoFusion, 3, "\t", "Orbit to Aut(S)-conjugacy");
            A0F := Orbits(S, A0F);
            Info(InfoFusion, 3, "\t", "Found");
            A0F := Filtered(A0F, X -> ForAll(A0, Y -> not Y in X));
            A0F := List(A0F, Representative);
            Append(A0, A0F);
            Info(InfoFusion, 3, "\t", Length(A0F), " new subs");
        od;

        A0 := Filtered(A0, X -> ForAll(L0, Y -> not IsConjugate(S, X, Y)));
        Append(L0, A0);

        if E in L0 or PE_FAST2(S0, E) or PE_SLOW2(S0, E) then 
            Info(InfoFusion, 2, "\t", "E is essential");
            Add(T, E);
        fi;
    od;

    return T;
end);
