LoadPackage("format");

InstallMethod(Holomorph, "method for finding holomorph", [IsPGroup], 
function(S)
    local AutS, AutS_nm, n;

    AutS := AutomorphismGroupPGroup(S, "Over");
    
    if AutS.glOrder = 1 then 
        AutS_nm := PcGroupAutPGroup(AutS);
        AutS := Group(AutS.agAutos);
        n := GroupHomomorphismByImagesNC(AutS_nm, AutS);
        SetAutomorphismGroup(S, AutS);
        SetNiceMonomorphism(AutS, InverseGeneralMapping(n));

        return SemidirectProduct(AutS_nm, n, S);
    else 
        AutS := ConvertHybridAutGroup(AutS);
        AssignNiceMonomorphismAutomorphismGroup(AutS, S);
        n := NiceMonomorphism(AutS);
        AutS_nm := Image(n);

        return SemidirectProduct(AutS_nm, RestrictedInverseGeneralMapping(n), S);
    fi;
end );

InstallMethod(Automizer, "method for automizer", [IsGroup, IsGroup], function(G, H)
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
end);

InstallGlobalFunction(OnQuotient, function(q)
    return function(t, x)
        return Image(q, PreImagesRepresentative(q,t)^x);
    end;
end );

InstallMethod(CentralizerMod, "method for groups", [IsGroup, IsGroup, IsGroup], function(G,A,U)
    local q;
    
    q := NaturalHomomorphismByNormalSubgroup(G,U);
    return Kernel(ActionHomomorphism(G, Image(q,A), OnQuotient(q)));
end );


InstallGlobalFunction(OnImage, function(n)
    return function(x, phi)
        return Image(phi, x);
    end;
end );

InstallGlobalFunction(OnImageNM, function(n)
    return function(x, phi)
        return Image(PreImagesRepresentative(n,phi), x);
    end;
end );


# Computes $O^{p'}(G)$
PrimeResidual := function(G,p)
    return NormalClosure(G, SylowSubgroup(G,p));
end;

# TODO: This should go to autpgrp package
PcSubAutPGroup := function(AutPC, A)
    local L;

    L := List(GeneratorsOfGroup(A), x -> ImageAutPGroup(AutPC!.autrec, AutPC, x));
    return Subgroup(AutPC, L);
end;

