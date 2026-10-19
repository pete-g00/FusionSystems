DeclareInfoClass("InfoFusion");
SetInfoLevel(InfoFusion, 4);

Automizer := function(G, H)
    local NGH, L, AutGH;

    NGH := Normalizer(G, H);
    L := List(SmallGeneratingSet(NGH), a -> ConjugatorAutomorphismNC(H, a));
    
    if IsEmpty(L) then 
        AutGH := Group(IdentityMapping(H));
    else 
        AutGH := Group(L);
    fi;

    SetIsGroupOfAutomorphisms(AutGH, true);
    SetAutomorphismDomain(AutGH, H);

    return AutGH;
end;

PrimeResidual := function(G, p)
	return NormalClosure(G, SylowSubgroup(G,p));
end;

ContainsStronglyPEmbeddedSubgroup := function(A,p)
	if PValuation(Size(A), p) = 0 then 
		return false;
	elif not (IsCyclic(SylowSubgroup(A,p)) or IsQuaternionGroup(SylowSubgroup(A,p)) or IsElementaryAbelian(SylowSubgroup(A,p))) then 
		return false;
	elif not IsTrivial(PCore(A,p)) then 
		return false;
	fi;

	if IsCyclic(SylowSubgroup(A,p)) or IsQuaternionGroup(SylowSubgroup(A,p)) then 
		return true;
	elif IsSolvable(A) then 
		return false;
	fi;

	# C_2^2 -> needs \SL_2(4)
	if PValuation(Size(A), 2) = 2 then 
		return Size(A) = 60 and IsSimple(A);
	# C_3^3 -> needs \SL_2(8)
	elif PValuation(Size(A), 2) = 3 then 
		return Size(A) = 504 and IsSimple(A);
	fi;

	return true;
end;

PcSubAutPGroup := function(AutPC, A)
    local L;

    L := List(GeneratorsOfGroup(A), x -> ImageAutPGroup(AutPC!.autrec, AutPC, x));
    return Subgroup(AutPC, L);
end;

PossibleAutFE := function(E)
    local   AutE, # Aut(E)
            InnE, # Inn(E)
            p, # the prime
            n, # the nice monomorphism for Aut(E)
            L, # possible choices for Aut_F(E)
            i, # current position in L
            AutFE, # possible Aut_F(E)
            A, # O_p(Aut_F(E))
            q, # quotient map Aut_F(E) -> Aut_F(E)/A
            OutFE, # quotient Aut_F(E)/A
            OutSE, # quotient Aut_S(E)/A
            OutE, # quotient Aut(E)/A
			B, #
			L0, # 
            M, # the maximal subgroups of OutFE
            C, # the conjugates of subgroups in M containing OutSE
            I, # positions of conjugates in C containing OutSE
            a, # counter of new automizers
            X; # a subgroup in C

    Info(InfoFusion, 2, "Finding valid automizer(s)");

    p := PrimePGroup(E);

    AutE := AutomorphismGroup(E);
    n := NiceMonomorphism(AutE);
    InnE := Automizer(E, E);
    AutE := NiceObject(AutE);

    if IsBound(AutE!.autrec) then 
        InnE := PcSubAutPGroup(AutE, InnE);
    else 
        InnE := Image(n, InnE);
    fi;

    L := [PrimeResidual(AutE,p)];
    i := 0;

    while i < Length(L) do 
        i := i+1;
        AutFE := L[i];
        A := PCore(AutFE,p);

        q := NaturalHomomorphismByNormalSubgroup(AutFE, A);
        
        OutFE := Image(q);
        Info(InfoFusion, 3, "\tFound section of order ", Size(OutFE));
        
        M := MaximalSubgroupClassReps(OutFE);
        Info(InfoFusion, 3, "\t\twhich has ", Length(M), " maximal subgroups");
        M := List(M, A -> PrimeResidual(A,p));
        M := List(M, A -> PreImage(q, A));

        a := 0;
        # Add missing G-conjugates
        for X in M do 
            if Index(X, PCore(X,p)) mod p = 0 and ForAll(L, T -> not IsConjugate(AutE, T, X)) then 
                a := a+1;
                Add(L, X);
            fi;
        od;
        Info(InfoFusion, 3, "\t\tTotal ", a, " possible automizer(s) up to Aut(E)-conjugacy");
    od;

    q := NaturalHomomorphismByNormalSubgroup(AutE, InnE);
    OutE := Image(q);
    L := List(L, A -> Image(q, A));
    Info(InfoFusion, 3, "\t", Length(L), " possible valid essential automizer(s) (mod p-core)");

    L := List(L, A -> ComplementClassesRepresentatives(A, PCore(A,p)));
    L := Filtered(L, A -> not IsEmpty(A));
    L := List(L, Representative);
	L := Filtered(L, A -> ContainsStronglyPEmbeddedSubgroup(A, p));
    Info(InfoFusion, 2, Length(L), " valid essential automizer(s)");

	return Set(List(L, X -> IdGroup(SylowSubgroup(X,p))));
end;
