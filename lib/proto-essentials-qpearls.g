SupportsQPearls := function(S0, arg...)
    local gl_ver, r, M,  e, S, p, q, AutS, AutS_PC, M_AutS, n, OnImage, C, N0, N, I, G, i, V, AutGV, AutSV, AutV, nV, NSyl, Cen, AutFV, AutFV_p, In, In_p, f, t, x;

    if Length(arg) = 0 then 
        gl_ver := false;
    else 
        gl_ver := arg[1];
    fi;

    p := PrimePGroup(S0);
    q := Size(Center(S0));
    
    r := NilpotencyClassOfGroup(S0);

    if Size(S0) <> q^(r+1) then 
        Info(InfoWarning, 1, "S is not generalised maximal class");
        return false;
    fi;
    
    AutS := AutomorphismGroupPGroup(S0);
    
    Info(InfoWarning, 1, "Aut(S) has order ", AutS.size);

    if AutS.size mod (q-1) <> 0 then 
        Info(InfoWarning, 1, "  which is too small");
        return false;
    fi;

    # TODO: Instead of semidirect product, maybe group action this (if solvable, ensure pc group)
    if AutS.glOrder = 1 then 
        Info(InfoWarning, 1, "Aut(S) is solvable");
        AutS_PC := PcGroupAutPGroup(AutS);
        AutS := ConvertHybridAutGroup(AutS);
        SetAutomorphismGroup(S0, AutS);

        t := GroupHomomorphismByImagesNC(AutS_PC, AutS);
        AutS := AutS_PC;

        if Exponent(AutS/PCore(AutS,p)) mod (q-1) <> 0 then 
            Info(InfoWarning, 1, "Aut(S)/O_p(Aut(S)) doesn't have the right element");
            return false;
        fi;

        Info(InfoWarning, 1, "Constructing semidirect product");
        G := SplitExtension(AutS, t, S0);
        Info(InfoWarning, 1, "Semidirect product constructed");

        S := ModuleOfExtension(G);
    else 
        Info(InfoWarning, 1, "Aut(S) is not solvable");
        AutS := ConvertHybridAutGroup(AutS);
        SetAutomorphismGroup(S0, AutS);

        Info(InfoWarning, 1, "Constructing semidirect product");
        G := SemidirectProduct(AutS, S0);
        Info(InfoWarning, 1, "Semidirect product constructed");

        S := Image(Embedding(G, 2));
        AutS := Image(Embedding(G, 1));

        if Exponent(AutS/PCore(AutS,p)) mod (q-1) <> 0 then 
            Info(InfoWarning, 1, "Aut(S)/O_p(Aut(S)) doesn't have the right element");
            return false;
        fi;
    fi;
    
    Info(InfoWarning, 1, "Finding gamma_1(S)");
    N := NormalSubgroups(S);
    N := Filtered(N, A -> Index(S,A) = q and NilpotencyClassOfGroup(A) < NilpotencyClassOfGroup(S0)-1);
    if Length(N) = 1 then 
        N := N[1];
    else 
        N := Filtered(N, A -> Size(Center(A)) = q);
        if Length(N) in [1, q+1] then 
            N := N[1];
        else 
            Info(InfoWarning, 1, "S is not generalised maximal class");
            return false;
        fi;
    fi;
    Info(InfoWarning, 1, "Check S splits over gamma_1(S)");
    
    C := ComplementClassesRepresentatives(S, N);
    if Length(C) = 0 then 
        Info(InfoWarning, 1, "S doesn't split over gamma_1(S)");
        return false;
    fi;
    Info(InfoWarning, 1, "S splits over gamma_1(S)");
    
    Info(InfoWarning, 1, "Number of choices for q-pearls up to S-class = ", Length(C));
    C := List(C, A -> Centralizer(S,A));
    C := Filtered(C, A -> Size(A) = q^2 and IsElementaryAbelian(A));;
    Info(InfoWarning, 1, "Number of possible q-pearls passing all tests = ", Length(C));

    if IsEmpty(C) then 
        return false;
    fi;

    N0 := List(C, A -> Normalizer(G, A));

    for i in [1..Length(N0)] do
        Info(InfoWarning, 1, "Looking at choice ", i);
        
        V := C[i];
        N := N0[i];

        if Exponent(N0[i]/PCore(N0[i],p)) mod (q-1) <> 0 then 
            Info(InfoWarning, 1, "Doesn't preserve any q-1");
            continue;
        fi;

        AutGV := Automizer(N,V);
        AutSV := Automizer(S,V);
        AutV := AutomorphismGroup(V);
        nV := NiceMonomorphism(AutV);

        AutV := Image(nV, AutV);
        AutGV := List(GeneratorsOfGroup(AutGV), a -> Image(nV, a));
        AutGV := Group(AutGV);
        AutSV := List(GeneratorsOfGroup(AutSV), a -> Image(nV, a));
        AutSV := Group(AutSV);

        NSyl := Normalizer(AutV, AutSV); # q^2 : (q-1)^2 extended
        if q <> p and IndexNC(NSyl, PCore(NSyl,p)) <> (q - 1)^2 * 2 then 
            Info(InfoWarning, 1, "Invalid structure of N_{Aut(V)}(Aut_S(V))/O_p(Aut_S(V)) : ", StructureDescription(NSyl));
            continue;
        fi;
        NSyl := ComplementClassesRepresentatives(NSyl, PCore(NSyl,p))[1]; # (q - 1)^2 extended

        if q <> p then 
            NSyl := First(SubgroupsOfIndexTwo(NSyl), IsAbelian); # (q - 1)^2
        fi;

        NSyl := ClosureGroup(AutSV, NSyl); # q^2 : (q - 1)^2 
        AutGV := ClosureGroup(AutGV, PCore(NSyl, p)); # add all p-maps (deals with conjugacy issues)
        
        # TODO: Can false positives exist here? E.g. [243, 30]
        Cen := Center(NSyl); # q-1
        AutFV := Centralizer(AutV, Cen); # GL(2, q)

        AutFV_p := PrimeResidual(AutFV, p); # SL(2, q)
        
        In := Intersection(AutGV, AutFV);
        In_p := Intersection(AutGV, AutFV_p);

        Info(InfoWarning, 1, "Intersecting N_{Aut(S)}(V) with GL_2(q) -> ", StructureDescription(In)); 
        Info(InfoWarning, 1, "Intersecting N_{Aut(S)}(V) with SL_2(q) -> ", StructureDescription(In_p)); # $(p-1 \times p-1) : (p^2-1)$?

        if (Size(In_p) mod (q - 1) = 0) or (gl_ver and Size(In) mod (q-1) = 0) then 
            return true;
        fi;
    od;

    return false;
end;
