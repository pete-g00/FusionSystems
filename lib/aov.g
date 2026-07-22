# TODO:
# * Integrate 2.2(h)
# * Add check for strongly 2-embedded subgroups in valid automizers
# * Join proto-essential radical checks for solvable/non-solvable
# * Some sort of general framework for aut-grp to deal with nice-monomorphism from autgrp-pgrp algorithm

# Compute the transfer homomorphism on H_1(-,Z), where H is a subgroup
# of G, but return the map from G to H/[H,H], not from G/[G,G]

# Return the trivial homomorphism from a group G to another group H
TrivialHomomorphism := function(G,H)
    return GroupHomomorphismByFunction(G,H, g->One(H));
end;

TransferHomomorphism := function(G, H, N)
    local piH, Hab, trans, gensG, imagegens, g, h;

    piH := NaturalHomomorphismByNormalSubgroup(H, N);
    Hab := Image(piH);
    trans := RightTransversal(G,H);
    gensG := GeneratorsOfGroup(G);
    
    imagegens := [];
    for g in gensG do
        h := Product(List(trans, t->t*g*trans[PositionCanonical(trans,(t*g))]^-1));
        Add(imagegens, Image(piH, h));
    od;
    
    return GroupHomomorphismByImagesNC(G,Hab, gensG, imagegens);
end;

# Currently the check of AOV 2.2(d) below combines the two cases of
# transfer on H_1(-,Z) and on H^1(-,Fp) into one function.
IsKernelOfTransfersDerivedSubgroup := function(S)
    local D, F, M;

    D := DerivedSubgroup(S);
    F := FrattiniSubgroup(S);
    M := MaximalSubgroups(S);

    return  Intersection(List(M, A -> Kernel(TransferHomomorphism(S,A, DerivedSubgroup(A))))) = D and 
            Intersection(List(M, A -> Kernel(TransferHomomorphism(S,A, FrattiniSubgroup(A))))) = F;
end;

SupportsReducedFusionSystems := function(S)
    local   D, # S'
            G, # holomorph of S
            i, # embedding of S into G
            S0, # image of S in G
            O, # \Omega(Z(S0))
            C, C0, # the proto-essential subgroups of S
            A, # semi-automorphism group of S
            E, # element in C
            Q, # semi-characteristic closure of [N_S(E), E] in E
            M, # [A, E]
            T, # \langle [A, S0], [A, E] \mid E in C \rangle
            SC; # the semi-characteristic subgroups of S

    if PrimePGroup(S) <> 2 then 
        Error("S is not a 2-group.");
    fi;

    D := DerivedSubgroup(S);

    if IsTrivial(CommutatorSubgroup(S, D)) then 
        Info(InfoFusion, 1, "(b) S has class <= 2");
        return false;
    fi;

    if IsCyclic(D) then 
        Info(InfoFusion, 1, "(b) S' is cyclic");
        return false;
    fi;
    
    if ForAny(MaximalSubgroups(S), IsAbelian) then 
        Info(InfoFusion, 1, "(a) has an index 2 subgroup that is abelian");
        return false;
    fi;
    
    if not IsKernelOfTransfersDerivedSubgroup(S) then
		Info(InfoDebug,2,"Failed 2.2(d)");
		return false;
    fi;

    G := Holomorph(S);
    i := Embedding(G, 2);
    
    S0 := Image(i, S);
    D := Image(i, D);
    
    # AOV test (c) - Either $\Omega(Z(S)) \leq S'$ OR $[\Omega(Z(S))S' : S'] > 2$ and $\Aut(S)$ is not a $2$-group
    O := Omega(Center(S0), 2);
    
    if not IsSubset(D, O) then 
        if Index(ClosureGroup(O, D), D) = 2 then 
            Info(InfoFusion, 1, "(c) [\\Omega(Z(S))S' : S'] = 2");
            return false;
        elif IsPGroup(G) then 
            Info(InfoFusion, 1, "(c) [\\Omega(Z(S))S' : S'] > 2, but Aut(S) is a p-group");
            return false;
        fi;
    fi;

    C := MainProtoEssentials(S, true);
    C := Filtered(C, X -> not (IsAbelian(X) and IsNormal(S, X))); # remove normal abelian
    if IsEmpty(C) then 
        Info(InfoFusion, 1, "C0 empty");
        return false;
    fi;

    C := MainProtoEssentials(S);
    C := Filtered(C, X -> not (IsAbelian(X) and IsNormal(S, X))); # remove normal abelian
    if Length(C) = 1 and IsNormal(G, Image(i,C[1])) then 
        Info(InfoFusion, 1, "(e) C has a unique characteristic subgroup");
        return false;
    fi;

    C := GenerateProtoEssentials(S, C);
    C := Filtered(C, X -> not (IsAbelian(X) and IsNormal(S, X))); # remove normal abelian
    C := Filtered(C, A -> not IsEmpty(PE_ValidAutomizers(S, A)));
    C := List(C, A -> Image(i, A));

    A := PrimeResidual(G, 2);
    A := ClosureGroup(S0, A);
    
    # characteristic in S to take Aut(S)-closure
    SC := Filtered(NormalSubgroups(S0), X -> IsNormal(G, X) and ForAll(C, E -> IsSubset(E, X) and IsSemicharacteristicSubgroup(E, X))); 
    if Length(SC) > 1 then 
        Info(InfoFusion, 1, "(g) There is a non-trivial subgroup semi-characteristic in every essential");
        return false;
    fi;

    if CommutatorSubgroup(A, S0) <> S0 then 
        T := CommutatorSubgroup(A, S0);
        for E in C do 
            M := CommutatorSubgroup(Normalizer(S0,E), E);
            IsPGroup(M); # the test doesn't run without this
            Q := SemicharacteristicClosure(E, M);
            T := ClosureGroup(T, Q);
            T := NormalClosure(A, T);
            if T = S0 then
                continue;
            fi;
        od;
        if T <> S0 then 
            Info(InfoFusion, 1, "(f) Semicharacteristic closure too small");
            return false;
        fi;
    fi;
    # TODO: Integrate 2.2(h)

    # Info(InfoDebug,2,"Checking no strongly fixed elements over Z...");
    # if not HasNoStronglyFixedElements(S, "Z") then
	# Info(InfoDebug,2,"Failed 2.2h1");
    #     return false;
    # fi;
    # Info(InfoDebug,2,"Checking no strongly fixed elements over Fp...");
    # if not HasNoStronglyFixedElements(S, "Fp") then
	# Info(InfoDebug,2,"Failed 2.2h2");
    #     return false;
    # fi;


    return true;
end;
