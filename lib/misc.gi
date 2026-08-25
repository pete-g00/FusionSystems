LoadPackage("format");

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

PcSubAutPGroup := function(AutPC, A)
    local L;

    L := List(GeneratorsOfGroup(A), x -> ImageAutPGroup(AutPC!.autrec, AutPC, x));
    return Subgroup(AutPC, L);
end;
