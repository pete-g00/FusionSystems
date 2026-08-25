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

# Compute the transfer homomorphism on H_1(-,Z), where H is a subgroup
# of G, but return the map from G to H/[H,H], not from G/[G,G]
InstallMethod(TransferHomomorphism, "method for transfer homomorphism from G to H/H'", 
    [IsGroup, IsGroup], function(G,H)
    local Hab, piH, trans, gensG, imagegens, g, h;
    
	piH := NaturalHomomorphismByNormalSubgroupNC(H,DerivedSubgroup(H));
	Hab := Image(piH);
    
    trans := RightTransversal(G,H);
    gensG := GeneratorsOfGroup(G);
    imagegens := [];
    
    for g in gensG do
        h := Product(List(trans, t->t*g*trans[PositionCanonical(trans,(t*g))]^-1));
        Add(imagegens,Image(piH, h));
    od;
    
    return GroupHomomorphismByImagesNC(G,Hab, gensG, imagegens);
end);

SecondCentre := function(S)
    local q;
    q := NaturalHomomorphismByNormalSubgroupNC(S, Centre(S));
    return PreImage(q, Centre(Image(q)));
end;

Zed0 := function(S)
    local Z2S, ZS, T, Zp, t, A;

    Z2S := SecondCentre(S);
    ZS := Centre(S);

    # Not sure whether computing a transversal is more efficient
    # overall or not but...
    T := RightTransversal(Z2S,ZS);

    # ... note [t, S] = [tz, S] for each z in Z(S), so we only need
    # check the commutator condition on a set of coset representatives
    # for Z(S) in Z_2(S).
    Zp := ZS;
    for t in T do
        A := Group(t);
        if Size(CommutatorSubgroup(S, A)) = 2 then 
            Zp := ClosureGroup(Zp, A);
            if Zp = Z2S then 
                continue;
            fi;
        fi;
    od;

    return Zp;
end;

GetC0FAST := function(S, Zed, R)
    local C0, I, i, E, x, ZS, Z2S;
    
    Info(InfoFusion, 2, "Finding C0");
    
    C0 := ClassesSolvableGroup(S, 0);
    C0 := Filtered(C0, a -> Order(a.representative) = 2);
    C0 := Filtered(C0, a -> a.centralizer <> S);
    C0 := Filtered(C0, a -> not (IsAbelian(a.centralizer) and IsNormal(S, a.centralizer)));

    I := [];
    
    for i in [1..Length(C0)] do 
        E := C0[i].centralizer;
        x := C0[i].representative;
        if not IsSubset(E, Zed) then 
            if Index(Normalizer(S,E), E) = 2 and not x in R then 
                Add(I, i);
            fi;
        else 
            Add(I, i);
        fi;
    od;

    C0 := List(I, i -> C0[i].centralizer);
    C0 := Orbits(S, C0);
    C0 := List(C0, Representative);
    Info(InfoFusion, 2, Length(C0), " subgroup(s) up to S-conjugacy passing 2.3(i)-(ii)");

    return Filtered(C0, A -> PE_FAST2(S, A));
end;

GetCFast := function(S, Zed, C0)
    local L, j, q, Q, C;

    L := LowerCentralSeries(S);
    # Deals with a bug in CompositionSeriesThrough
    L := CSThru(S, L);
    
    j := Position(L, DerivedSubgroup(S));
    L := L{[j+1..Length(L)]};

    Info(InfoFusion, 2, "Finding C");
    Info(InfoFusion, 2, Length(L), " iterations");
    
    q := List(L, A -> NaturalHomomorphismByNormalSubgroupNC(S,A));
    
    Q := List(q, Image);
    C := List(Q, A -> ClassesSolvableGroup(A,0));
    C := List(C, A -> Filtered(A, a -> Order(a.representative) = 2));
    C := List([1..Length(C)], i -> Filtered(C[i], a -> a.centralizer <> Q[i]));
    C := List(C, A -> List(A, a -> a.centralizer));
    C := List([1..Length(C)], i -> List(C[i], A -> PreImage(q[i], A)));
    
    C := Flat(C);
    C := Filtered(C, A -> not (IsAbelian(A) and IsNormal(S, A)));
    C := Filtered(C, A -> IsSubset(A, Zed));
    C := Orbits(S, C);
    C := List(C, Representative);

    C := Filtered(C, A -> ForAll(C0, B -> not IsConjugate(S, A, B)));
    Info(InfoFusion, 2, Length(C), " new subgroup(s) up to S-conjugacy passing 2.3(i)-(ii)");

    return Filtered(C, A -> PE_FAST2(S, A));
end;

InstallMethod(SupportsReducedFusionSystems, "method to see whether S supports reduced fusion systems", 
    [IsPGroup], function(S)
local   D, # S'
        Zed, # Z_0
        R, # C_S(Z_2(S))
        O, # \Omega(Z(S))
        C0, # $C_0$ (passing PE_FAST)
        AutS, # $\Aut_0(S)$
        IsAut2Group, # is Aut(S) a 2-group?
        C, # $C$ (passing PE_FAST)
        K0, # kernel of the transfer homomorphism for groups in C0
        K, # kernel of the transfer homomorphism for groups in C
        I0, # subgroups in C0 passing PE_SLOW
        I; # subgroups in C passing PE_SLOW

    if NilpotencyClassOfGroup(S) <= 2 then 
        Info(InfoFusion, 1, "(a) S has class <= 2");
        return false;
    fi;

    D := DerivedSubgroup(S);

    # Check AOV 2.2(b)
    if IsCyclic(D) then 
        Info(InfoFusion, 1, "(b) S' is cyclic");
        return false;
    fi;
    
    # Check AOV 2.2(a) -> C_S(Z_2(S)) cannot be an index 2 abelian subgroup of S
    R := Centralizer(S, SecondCentre(S));
    if Index(S,R) = 2 and IsAbelian(R) then 
        Info(InfoFusion, 1, "(c) C_S(Z_2(S)) index 2 abelian");
    fi;
    
    # AOV test (c) - Either $\Omega(Z(S)) \leq S'$ OR $[\Omega(Z(S))S' : S'] > 2$ and $\Aut(S)$ is not a $2$-group
    O := Omega(Center(S), 2);
    if Index(O, Intersection(O, D)) = 2 then 
        Info(InfoFusion, 1, "(d) [\\Omega(Z(S)) : \\Omega(Z(S)) \\cap S'] = 2");
        return false;
    fi;

    Info(InfoFusion, 2, "Finding proto-essentials (FAST)");
    # THE FAST TESTS
    Zed := Zed0(S);
    C0 := GetC0FAST(S, Zed, R);
    if IsEmpty(C0) then 
        Info(InfoFusion, 1, "(e) C0 empty");
        return false;
    fi;

    AutS := InitAutomorphismGroupOver(S);
    if AutS.size = 1 or (IsPrimePowerInt(AutS.size) and SmallestRootInt(AutS.size) = 2) then 
        IsAut2Group := true;
        Info(InfoFusion, 2, "\\Aut_0(S) is a 2-group");
    else
        IsAut2Group := false;
        Info(InfoFusion, 2, "\\Aut_0(S) is not a 2-group");
    fi;
    
    if IsAut2Group and not IsSubset(D, O) then 
        Info(InfoFusion, 1, "(f) \\Omega(Z(S)) \\nleq S'");
        return false;
    fi;

    C := GetCFast(S, Zed, C0);
    Info(InfoFusion, 1, Length(C)+Length(C0), " subgroup(s) passed the fast tests");

    if Length(C)+Length(C0)= 1 and IsAut2Group then
        Info(InfoFusion, 1, "(g) S has a unique conjugacy class of proto-essentials");
        return false;
    elif Length(C)+Length(C0) = 1 and IsNormal(S, C0[1]) then 
        Info(InfoFusion, 1, "(h) S has a unique characteristic proto-essential");
        return false;
    fi;
    
    if IsAut2Group then 
        K0 := List(C0, A -> Kernel(TransferHomomorphism(S, A)));
        K := List(C, A -> Kernel(TransferHomomorphism(S, A)));
        if Size(Intersection(Flat([K0, K]))) > Size(DerivedSubgroup(S)) then 
            Info(InfoFusion, 1, "(i) Intersection of transfer kernel larger than the derived subgroup");
            return false;
        fi;
    fi;

    # THE SLOW TESTS
    Info(InfoFusion, 2, "Finding proto-essentials (SLOW)");
    I0 := PositionsProperty(C0, E -> PE_SLOW2(S, E));
    if IsEmpty(I0) then 
        Info(InfoFusion, 1, "(e) C0 empty");
        return false;
    elif ForAll(I0, i -> IsCharacteristicSubgroup(C0[i], O)) then
        Info(InfoFusion, 1, "(j) Every subgroup in C0 has \\Omega(Z(S)) characteristic");
        return false;
    fi;

    I := PositionsProperty(C, E -> PE_SLOW2(S, E));
    Info(InfoFusion, 2, Length(I)+Length(I0), " subgroup(s) passed the slow tests");
    if Length(I)+Length(I0)= 1 and IsAut2Group then
        Info(InfoFusion, 1, "(g) S has a unique conjugacy class of proto-essentials");
        return false;
    elif Length(I)+Length(I0) = 1 and IsNormal(S, C0[I0[1]]) then 
        Info(InfoFusion, 1, "(h) S has a unique characteristic proto-essential");
        return false;
    fi;

    C0 := C0{I0};
    C := C{I};

    AutS := AutomorphismGroup(S);
    if not IsAut2Group and IsPGroup(AutS) then 
        Info(InfoFusion, 2, "\\Aut(S) 2-group, but \\Aut_0(S) not a 2-group");
        if not IsSubset(D, O) then 
            Info(InfoFusion, 1, "(f) \\Omega(Z(S)) \\nleq S'");
            return false;
        fi;
        K0 := List(C0, A -> Kernel(TransferHomomorphism(S, A)));
        K := List(C, A -> Kernel(TransferHomomorphism(S, A)));
        if Size(Intersection(Flat([K0, K]))) > Size(DerivedSubgroup(S)) then 
            Info(InfoFusion, 1, "(i) Intersection of transfer kernel larger than the derived subgroup");
            return false;
        fi;
    fi;

    C := GenerateProtoEssentials(S, Flat([C, C0]));
    Info(InfoFusion, 2, "Generated ", Length(C), " proto-essentials");

    if ForAny(CharacteristicSubgroups(S), A -> A <> TrivialSubgroup(S) 
        and ForAll(C, E -> IsSubset(E, A) and IsCharacteristicSubgroup(E, A))) then 
        Info(InfoFusion, 1, "(k) There exists a non-trivial subgroup characteristic in every proto-essential and S");
        return false;
    fi;

    return true;
end);
