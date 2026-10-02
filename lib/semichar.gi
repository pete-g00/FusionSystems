InstallMethod(SemiAutomorphismGroup, "method to construct the semi automorphism group", [IsPGroup],
function(S)
    local p, AutS, AutSp, n;

    p := PrimePGroup(S);
    AutS := AutomorphismGroup(S);
    n := NiceMonomorphism(AutS);

    AutS := Image(n, AutS);
    AutSp := PResidual(AutS, p);
    AutSp := PreImage(n, AutSp);
    
    SetIsGroupOfAutomorphisms(AutSp, true);
    SetNiceMonomorphism(AutSp, n);

    return AutSp;
end );

InstallMethod(IsSemicharacteristicSubgroup, "method to check whether a subgroup is semicharacteristic", [IsPGroup, IsPGroup], function(S, X)
    local AutS;

    AutS := SemiAutomorphismGroup(S);
    return ForAll(GeneratorsOfGroup(AutS), x -> Image(x, X) = X);
end);

InstallMethod(SemicharacteristicSubgroups, "method for finding all semicharacteristic subgroups", [IsPGroup], function(S)
    local N;

    N := NormalSubgroups(S);
    return Filtered(N, A -> IsSemicharacteristicSubgroup(S,A));
end);

InstallMethod(SemicharacteristicClosure, "method for finding semicharacteristic closure for a subgroup", [IsPGroup, IsPGroup], function(S, X)
    local N;

    if IsSemicharacteristicSubgroup(S, X) then 
        return X;
    fi;

    N := NormalSubgroups(S);
    N := Filtered(N, A -> IsSubset(A, X) and IsSemicharacteristicSubgroup(S, A));

    return Intersection(N);
end);
