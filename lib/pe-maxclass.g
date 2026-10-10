# TODO: We could also have index p abelian/extraspecial in some cases
SupportsPearls := function(S)
    local p, r, AutS, C;

    p := PrimePGroup(S);
    r := NilpotencyClassOfGroup(S);

    if Size(S) <> p^(r+1) then 
        Info(InfoWarning, 1, "S is not maximal class");
        return false;
    fi;
    
    AutS := AutomorphismGroup(S);
    
    Info(InfoWarning, 1, "Aut(S) has order ", Size(AutS));

    if Size(AutS) mod (p-1) <> 0 then 
        Info(InfoWarning, 1, "  which is too small");
        return false;
    fi;

    C := ClassesSolvableGroup(S, 0);
    C := Filtered(C, x -> Order(x.representative) = p and x.centralizer <> S);
    C := List(C, x -> x.centralizer);

    C := Orbits(S, C);
    C := List(C, Representative);
    C := Filtered(C, A -> IsElementaryAbelian(A) and Size(A) = p^2);

    if Length(C) = 0 then 
        Info(InfoWarning, 1, "No choice for pearls");
        return false;
    fi;
    Info(InfoWarning, 1, Length(C), " choice(s) for pearls");

    return ForAny(C, V -> FindSmallestBorel(S, PrimeResidual(AutomorphismGroup(V), p)) <> fail);
end;

# Choices would be:
# - extraspecial index p -> only for the $p^{p+1}$ case
# - abelian index p -> only allowed when the abelian sub is eab OR homocyclic (?)
