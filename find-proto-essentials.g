DeclareInfoClass("InfoFusion");
SetInfoLevel(InfoFusion, 1);

Automizer := function(G, H)
    local NGH, L, AutGH;

    NGH := Normalizer(G, H);
    if IsTrivial(NGH) then 
        return Group(IdentityMapping(H));
    fi;

    L := List(SmallGeneratingSet(NGH), a -> ConjugatorAutomorphismNC(H, a));
    if IsEmpty(L) then 
        return Group(IdentityMapping(H));
    fi;

    AutGH := Group(L);

    SetIsGroupOfAutomorphisms(AutGH, true);
    SetAutomorphismDomain(AutGH, H);

    return AutGH;
end;

OnQuotient := function(q)
    return function(t, x)
        return Image(q, PreImagesRepresentative(q,t)^x);
    end;
end;

# Computes C_G(A/U)
StepCentralizer := function(G, A, U)
    local q;
    
    q := NaturalHomomorphismByNormalSubgroup(G,U);
    return Kernel(ActionHomomorphism(G, Image(q,A), OnQuotient(q)));
end;

# $C_{N_S(E)}(E/\Phi(E)) \leq E$
IsProtoEssentialSubgroup_Frat := function(S, E)
    # Specific case when $C_{N_S(E)}(E/\Phi(E)) = N_S(E)$
    if CommutatorSubgroup(Normalizer(S,E), E) = FrattiniSubgroup(E) then 
        return false;
    fi;
    # TODO: use exponents analysis for $E/\Phi(E)$ by the action of $S$?
    return IsSubset(E, StepCentralizer(Normalizer(S,E),E,FrattiniSubgroup(E)));
end;

IsProtoEssentialSubgroup_OutSE := function(S, E)
    local p, r, NSE, n, log_pr, OutSE;

    p := PrimePGroup(S);

    r := Rank(E);
    NSE := Normalizer(S,E);
    n := PValuation(IndexNC(NSE,E), p);

    if r < n^2 then 
        return -1;
    fi;

    log_pr := Int(Ceil(Log2(Float(r))/Log2(Float(p))));

    OutSE := NSE/E;

    if IsCyclic(OutSE) then 
        if PValuation(Size(OutSE), p) <= log_pr then 
            return 0;
        else 
            return -1;
        fi;
    fi;

    # PSL(2,p^n)
    if IsElementaryAbelian(OutSE) then 
        if 2*PValuation(Size(OutSE),p) <= r then 
            return 1;
        else 
            return -1;
        fi;
    fi;

    if p = 2 then 
        # TODO: Code this
    fi;

    if p = 3 then 
        # 3^{1+2}_-
        if Size(OutSE) = 27 and IdGroup(OutSE) = [27,4] then 
            return r >= 6;
        fi;

        # ^2 G_2(q)
        # TODO: Code this
    fi;

    # PSU(3,p^n)
    if p >= 3 and n mod 3 = 0 and Exponent(OutSE) = p and 
        Length(Set([Center(OutSE), DerivedSubgroup(OutSE), FrattiniSubgroup(OutSE)])) = 1 and 
        NilpotencyClassOfGroup(OutSE) = 2 and 
        IsElementaryAbelian(Center(OutSE)) and Size(Center(OutSE)) = p^(2*n/3) and
        HasElementaryAbelianFactorGroup(OutSE, Center(OutSE)) then 
        if r >= 6*n then 
            return 2;
        else 
            return -1;
        fi;
    fi;

    return -1;
end;

IsProtoEssentialSubgroup_AutSize := function(S, E, i, AutE_order)
    local p, OutSE_order, n, r;

    p := PrimePGroup(S);

    OutSE_order := Index(Normalizer(S,E), E);
    n := PValuation(OutSE_order, p);
    r := Rank(E);

    if i=0 then 
        if p = 2 then 
            return true;
        # no group of order q or 2q has a strongly p-embedded subgroup
        elif IsPrimePowerInt(AutE_order) or IsPrimePowerInt(AutE_order/2) then 
            return false;
        # the only group of order 4q that has a strongly p-embedded subgroup is Alt(4) at p=3
        elif p >= 5 and IsPrimePowerInt(AutE_order/4) then
            return false;
        fi;
    fi;
    # eab case
    if (i=0 and n=1) or i=1 then 
        if AutE_order mod Size(PSL(2, p^n)) = 0 then 
            return true;
        # TODO: Also check for rank
        # Alt(2p)
        elif p >= 5 and AutE_order mod Factorial(2*p)/2 = 0 then 
            return true;
        elif p = 3 then 
            # TODO: Also check for rank
            # M11, PSL(3,4)
            return ForAny([7920, 20160], a -> AutE_order mod a = 0);
        elif p = 5 then 
            # ^2F_4(2)' and Fi_22
        fi;
        return false;
    # PSU(3,p^n)
    elif i=2 then 
        return AutE_order mod Size(PSU(3,p^(n/3))) = 0;
    fi;

    return false;
end;

PcSubAutPGroup := function(AutPC, A)
    local Exp, A_m;
    
    Exp := List(GeneratorsOfGroup(A), x -> ExponentsAutPGroup(AutPC!.autrec, x));
    
    if fail in Exp then 
        return fail;
    fi;
    
    A_m := List(Exp, a -> MappedVector(a, GeneratorsOfGroup(AutPC)));
    return Subgroup(AutPC, A_m);
end;

# Minor change to the actual function ExponentsAutPGroup 
# that allows us to not crash when base is not in Source(B.agHomom)
ExponentsAutPGroup_ := function ( B, auto )
    local exps, imgs, perm, news, tmpa, j, e, s, n, subs, base;

    if not IsBound(B.agHomom) then 
        return fail;
    fi;

    exps := List( B.agAutos, x -> 0);
    imgs := List( B.gens, x -> ExponentsOfPcElement( B.spec, x ^ auto ));
    base := imgs{[ 1 .. B.rank ]}{[ 1 .. B.rank ]};
    if base <> IdentityMat( B.rank ) then
        base := base * One( B.field );
        if not base in Source( B.agHomom ) then
            return fail;
        fi;
        perm := Image( B.agHomom, base );
        news := ExponentsOfPcElement( B.agTopfc, perm );
        exps{[ 1 .. Length( news ) ]} := news;
        tmpa := MappedVector( news, B.agAutos{[ 1 .. Length( news ) ]} );
        auto := tmpa ^ -1 * auto;
    fi;
    imgs := List( B.gens, x -> ExponentsOfPcElement( B.spec, x ^ auto ));
    for j in [ 1 .. B.rank ] do
        imgs[j][j] := 0;
    od;
    e := Minimum( List( imgs, PositionNonZero ) );
    while e <= Length( B.spec ) do
        j := LGLayers( B.spec )[e];
        s := LGFirst( B.spec )[j];
        n := LGFirst( B.spec )[j + 1];
        base := Concatenation( imgs{[ 1 .. B.rank ]}{[ s .. (n - 1) ]} ) * One( B.field );
        s := PositionSorted( B.layer, j );
        n := PositionSorted( B.layer, j + 1 );
        subs := B.bases{[ s .. n - 1 ]};
        news := IntVecFFE( SolutionMat( subs, base ) );
        exps{[ s .. n - 1 ]} := news;
        tmpa := MappedVector( news, B.agAutos{[ s .. n - 1 ]} );
        auto := tmpa ^ -1 * auto;
        imgs := List( B.gens, x -> ExponentsOfPcElement( B.spec, x ^ auto ));
        for j in [ 1 .. B.rank ] do
            imgs[j][j] := 0;
        od;
        e := Minimum( List( imgs, PositionNonZero ) );
    od;
    return exps;
end;

# i -> a description of what the Syl-p sub is:
# 0 : cyclic
# 2 : eab
# 3 : Syl-p of PSU_3(p^n)
# (MORE TO COME)
IsProtoEssentialSubgroup_Aut := function(S, E, i)
    local p, OutSE, AutSE, AutE, AutE_PC, AutEp, G, Exp, n, C, AutSE_m;

    p := PrimePGroup(S);

    # EAB cannot be refined here
    if IsElementaryAbelian(E) then 
        Info(InfoFusion, 1, "Is EAB");
        return true; 
    fi;

    OutSE := Normalizer(S,E)/E;
    AutSE := Automizer(S,E);
    Info(InfoFusion, 1, Concatenation(List([1..50], i -> "-")));
    Info(InfoFusion, 1, "Constructing Aut(E) with OutSE of type ", i, " and order ", Size(OutSE), 
        " with [Rank(E), Class(E)] = ", [Rank(E), NilpotencyClassOfGroup(E)]);
    
    AutE := AutomorphismGroupPGroup(E, "Over");
    Info(InfoFusion, 1, "  Aut(E) has order ", AutE.size);

    if AutE.glOrder = 1 then 
        Info(InfoFusion, 1, "  Aut(E) is soluble");
    
        if i > 0 then 
            Info(InfoFusion, 1, "Invalid - Out_S(E) not cyclic");
            Info(InfoFusion, 1, Concatenation(List([1..50], i -> "_")));
            return false;
        fi;

        # check that the size of the automorphism group is valid
        if not IsProtoEssentialSubgroup_AutSize(S, E, i, AutE.size) then 
            Info(InfoFusion, 1, "Invalid size of aut group");
            Info(InfoFusion, 1, Concatenation(List([1..50], i -> "_")));
            return false;
        fi;
    else 
        Info(InfoFusion, 1, "  Aut(E) is not soluble");

        if IsBound(AutE.glOper) and i > 0 then 
            G := Group(AutE.glOper);
            C := CompositionSeries(G);

            if ForAll([1..Length(C)-1], j -> not IsProtoEssentialSubgroup_AutSize(S, E, i, IndexNC(C[j], C[j+1]))) then 
                Info(InfoFusion, 1, "No valid composition factor with the right size");
                Info(InfoFusion, 1, Concatenation(List([1..50], i -> "_")));
                return false;
            fi;
        fi;
    fi;

    AutE_PC := PcGroupAutPGroup(AutE);
    AutEp := PCore(AutE_PC, p);
    
    if AutE.glOrder = 1 and IndexNC(AutE_PC, AutEp) mod Size(OutSE) <> 0 then 
        Info(InfoFusion, 1, "Out_S(E) cannot project onto Aut(E)/O_p(Aut(E))");
        Info(InfoFusion, 1, Concatenation(List([1..50], i -> "_")));
        return false;
    elif AutE.glOrder = 1 then 
        Info(InfoFusion, 1, "  Out_S(E) can project onto Aut(E)/O_p(Aut(E))");
    fi;

    Exp := List(GeneratorsOfGroup(AutSE), x -> ExponentsAutPGroup_(AutE_PC!.autrec, x));
    
    if ForAll(Exp, a -> a <> fail) then 
        AutSE_m := List(Exp, a -> MappedVector(a, GeneratorsOfGroup(AutE_PC)));
        AutSE_m := Subgroup(AutE_PC, AutSE_m);
        
        # Aut_S(E) \cap O_p(\Aut(E)) = Inn(E)
        if Size(Intersection(AutSE_m, AutEp)) <> IndexNC(E, Center(E)) then 
            Info(InfoFusion, 1, "Cannot be radical");
            Info(InfoFusion, 1, Concatenation(List([1..50], i -> "_")));
            return false;
        fi;
        
        # Nothing more to be done if that sub was all we wanted
        if AutE.glOrder = 1 then 
            Info(InfoFusion, 1, "Can be radical");
            Info(InfoFusion, 1, Concatenation(List([1..50], i -> "_")));

            AutE := ConvertHybridAutGroup(AutE);
            SetIsGroupOfAutomorphisms(AutE, true);
            SetAutomorphismDomain(AutE, E);
            return true;
        else 
            Info(InfoFusion, 1, "  Can be radical with respect to the ag-maps");
        fi;
    else 
        Info(InfoFusion, 1, "  Aut_S(E) has gl-maps");
    fi;

    AutE := ConvertHybridAutGroup(AutE);
    SetIsGroupOfAutomorphisms(AutE, true);
    SetAutomorphismDomain(AutE, E);

    Info(InfoFusion, 1, "  Finding nice monomorphism for Aut(E)");
    AssignNiceMonomorphismAutomorphismGroup(AutE, E);
    Info(InfoFusion, 1, "  Computed");
    n := NiceMonomorphism(AutE);

    AutSE := Image(n, AutSE);
    AutE := Image(n, AutE);
    AutEp := PCore(AutE, p);
    

    # Aut_S(E) \cap O_p(\Aut(E)) = Inn(E)
    if Size(Intersection(AutSE, AutEp)) <> IndexNC(E, Center(E)) then 
        Info(InfoFusion, 1, "Cannot be radical");
        Info(InfoFusion, 1, Concatenation(List([1..50], i -> "_")));
        return false;
    fi;
    Info(InfoFusion, 1, "Can be radical");
    Info(InfoFusion, 1, Concatenation(List([1..50], i -> "_")));

    return true;
end;

IsProtoEssentialSubgroup := function(S, E)
    local i;
    
    if S = E or not IsSubset(E, Centralizer(S,E)) then 
        return false;
    fi;

    if not IsProtoEssentialSubgroup_Frat(S, E) then 
        return false;
    fi;

    i := IsProtoEssentialSubgroup_OutSE(S, E);
    if i=-1 then 
        return false;
    fi;

    # DO LIFT TEST BEFORE

    return IsProtoEssentialSubgroup_Aut(S, E, i);
end;

C0 := function(S)
    local C;

    C := ClassesSolvableGroup(S, 0);
    C := List(C, A -> A.centralizer);
    C := Orbits(S, C);
    C := List(C, Representative);

    return ForAny(C, A -> IsProtoEssentialSubgroup(S,A));
end;
