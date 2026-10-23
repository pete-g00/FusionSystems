InstallMethod(Automizer, "method for groups", [IsGroup, IsGroup], function(G, H)
    local NGH, L, AutGH;

    if IsGroupOfAutomorphisms(G) then 
        TryNextMethod();
    fi;

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


InstallGlobalFunction(OnImage, function(x, phi)
    return Image(phi, x);
end );

InstallGlobalFunction(OnImageNM, function(n)
    return function(x, phi)
        return Image(PreImagesRepresentative(n,phi), x);
    end;
end );

InstallGlobalFunction(OnImageTuples, function(L, phi)
    return List(L, x -> OnImage(x, phi));
end );

InstallGlobalFunction(OnImageTuplesNM, function (n)
    return function (L, phi)
        return List(L, x -> OnImageNM(n)(x, phi));
    end;
end);

InstallMethod(RestrictedHomomorphism,  "method for restricting isomorphism to another homomorphism", 
    [IsGroupHomomorphism, IsGroup], function(phi, T)
    local g, h, T0;

    g := GeneratorsOfGroup(T);
    h := List(g, x -> Image(phi,x));
    T0 := Image(phi, T);

    return GroupHomomorphismByImagesNC(T, T0, g, h);
end );

InstallMethod(RestrictedAutomorphism,  "method for restricting isomorphism to an automorphism", 
    [IsGroupHomomorphism and IsBijective, IsGroup], function(phi, T)
    local g, h;

    Assert(0, Image(phi,T) = T);
    
    g := GeneratorsOfGroup(T);
    h := List(g, x -> Image(phi,x));

    return GroupHomomorphismByImagesNC(T, T, g, h);
end );

InstallOtherMethod(Automizer, "automizer for automorphism groups", 
    [IsGroupOfAutomorphismsFiniteGroup, IsGroup and IsFinite], function(AutG, H)
    local n, AutG0, g, h, AutH;

    n := NiceMonomorphism(AutG);
    AutG := Image(n, AutG);

    AutG0 := Stabilizer(AutG, H, OnImageNM(n));
    AutG0 := PreImage(n, AutG0);

    g := GeneratorsOfGroup(AutG0);
    h := List(g, phi -> RestrictedAutomorphism(phi, H));

    AutH := Group(h);
    
    SetIsGroupOfAutomorphismsFiniteGroup(AutH, true);
    SetAutomorphismDomain(AutH, H);
    
    return AutH;
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

CSThru :=  function(G,normals)
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
        

        cs:=Concatenation(new,cs{[post+1..Length(cs)]});
        fi;
    od;

    return cs;
end;

# Family predicates matching a group of automorphisms of some group S with a
# subgroup, respectively an element, of S. These never hold for the arguments
# of the library methods, which come from a single family.
BindGlobal("FS_IsAutGroupAndSubgroupFamilies", function(FamA, FamP)
    return HasElementsFamily(FamA) and HasElementsFamily(FamP)
        and FamSourceEqFamElm(ElementsFamily(FamA), ElementsFamily(FamP));
end);

BindGlobal("FS_IsAutGroupAndElementFamilies", function(FamA, FamElm)
    return HasElementsFamily(FamA)
        and FamSourceEqFamElm(ElementsFamily(FamA), FamElm);
end);

# $\Aut_\calF(E)^g$ for some $g \in S$ and $E \leq S$
InstallOtherMethod(\^, "method to conjugate automorphism group by an element of an overgroup",
    FS_IsAutGroupAndElementFamilies,
    [IsGroupOfAutomorphisms, IsMultiplicativeElementWithInverse], function(Aut0, g)
    local E, c, t, G;

    E := AutomorphismDomain(Aut0);
    c := ConjugatorIsomorphism(E, g);
    t := List(GeneratorsOfGroup(Aut0), x -> InverseGeneralMapping(c) * x * c);
    G := Group(t);

    SetIsGroupOfAutomorphismsFiniteGroup(G, true);
    SetAutomorphismDomain(G, E^g);

    return G;
end );

InstallOtherMethod(\^, "method to conjugate automorphism group by some map from an overgroup",
    [IsGroupOfAutomorphisms, IsGroupHomomorphism and IsBijective], function(Aut0, phi)
    local E, c, t, G;

    # for phi in Aut(E) this is ordinary conjugation, done by the library
    if Source(phi) = AutomorphismDomain(Aut0) then
        TryNextMethod();
    fi;

    E := AutomorphismDomain(Aut0);
    c := RestrictedHomomorphism(phi, E);
    t := List(GeneratorsOfGroup(Aut0), x -> InverseGeneralMapping(c) * x * c);
    G := Group(t);

    SetIsGroupOfAutomorphismsFiniteGroup(G, true);
    SetAutomorphismDomain(G, Image(c, E));

    return G;
end);

IsInvariant := function(A,P)
    # VALID ONLY FOR FINITE P (for infinite P, need to also check x^(a^-1) in P)
    # Elements of A should be allowed to act on elements of P via
    # exponentiation, e.g. A is a subgroup of the automorphism group
    # of a group containing P as a subgroup, or A is a group acting on
    # a set of which P is a subset
    if ForAll(GeneratorsOfGroup(A), 
            a->ForAll(GeneratorsOfGroup(P), x->x^a in P)) then
        return true;
    fi;
    return false;
end;

# Computes the smallest A-invariant subgroup of the automorphism
# domain of A containing P. 
InvariantClosure := function(A,P)
    local S, gensA, gensP, gensN, N, a, x, cnj;
    if IsGroupOfAutomorphisms(A) then
        S := AutomorphismDomain(A);
    else 
        Error(A, "must be a group of automorphisms.");
    fi;
    if not IsSubgroup(S,P) then
        Error(A, "must be a group of automorphisms of a group containing", P, "as a subgroup");
    fi;
    gensA := GeneratorsOfGroup(A);
    N := P;
    while not IsInvariant(A,N) do
        gensN := GeneratorsOfGroup(N);
	    for a in gensA do
	        for x in gensN do
	            cnj := x^a;
	            if not cnj in N then
	                N := ClosureGroup(N,cnj);
	            fi;
	        od;
	    od;
    od;
    return N;
end;

# Computes the commutator subgroup of a subgroup A of automorphism
# group of S with a subgroup of S. Currently only implemented when the
# subgroup is A-invariant. The routine uses the fact (presumably
# true!) that in this case [A,P] is the smallest A-invariant normal
# subgroup of P containing all commutators x^-1*x^a of generators x of
# P with generators a of A. 

InstallOtherMethod(CommutatorSubgroup, "method for aut-group",
    FS_IsAutGroupAndSubgroupFamilies,
    [IsGroupOfAutomorphisms, IsGroup], function(A, P)
    local C, a, x, c;

    if not IsSubgroup(AutomorphismDomain(A), P) then
        Error(A, "must act on a group of which", P, "is a subgroup");
    elif not IsInvariant(A,P) then
        Error(P, "should be", A, "-invariant");
    fi;

    C := TrivialSubgroup(P);
    for a in GeneratorsOfGroup(A) do
        for x in GeneratorsOfGroup(P) do
            c := x^-1*x^a;
            if not c in C then
                C := ClosureGroup(C,c);
            fi;
        od;
    od;
    
    return InvariantClosure(A,NormalClosure(P,C));
end );

# Compute the transfer homomorphism on H_1(-,Z), where H is a subgroup
# of G, but return the map from G to H/[H,H], not from G/[G,G]

InstallMethod(TransferHomomorphism, "transfer homomorphism", 
    [IsGroup, IsGroup], function(G,H)
    local  Hab, piH, trans, gensG, imagegens, g, h;
    
    piH := NaturalHomomorphismByNormalSubgroupNC(H,DerivedSubgroup(H));
	Hab := Image(piH);
    
    if Size(Hab) = 1 then
        return GroupHomomorphismByImagesNC(G,Hab);
    fi;
    
    trans := RightTransversal(G,H);
    gensG := GeneratorsOfGroup(G);
    imagegens := [];

    for g in gensG do
        h := Product(List(trans, t->t*g*trans[PositionCanonical(trans,(t*g))]^-1));
        Add(imagegens,Image(piH, h));
    od;
    
    return GroupHomomorphismByImages(G,Hab, gensG, imagegens);
end );

# Compute the transfer homomorphism on H_1(-,F_p), where H is a
# p-subgroup of G, but return the map from G to H/Phi(H), not from
# G/Phi(G) to H/Phi(H). Only coded for H a p-group.

InstallMethod(TransferHomomorphismFp, "transfer homomorphism (Frattini version)", 
    [IsGroup, IsPGroup], function(G,H)
    local p, Habp, piH, trans, gensG, imagegens, g, h;
    
    p := PrimePGroup(H);
	piH := NaturalHomomorphismByNormalSubgroupNC(H,FrattiniSubgroup(H));
	Habp := Image(piH);
    
    if Size(Habp) = 1 then
        return GroupHomomorphismByImagesNC(G,Habp);
    fi;

    trans := RightTransversal(G,H);
    gensG := GeneratorsOfGroup(G);
    imagegens := [];
    
    for g in gensG do
        h := Product(List(trans, t->t*g*trans[PositionCanonical(trans,(t*g))]^-1));
        Add(imagegens,Image(piH, h));
    od;
    
    return GroupHomomorphismByImages(G,Habp, gensG, imagegens);
end );

InstallMethod(SemiAutomorphismGroup, "method for a p-group", 
    [IsPGroup], function(S)
    local p, AutS, InnS, AutSp, n;

    p := PrimePGroup(S);

    AutS := AutomorphismGroup(S);
    n := NiceMonomorphism(AutS);
    AutS := Image(n, AutS);
    
    InnS := InnerAutomorphismGroup(S);
    InnS := n(InnS);

    AutSp := PResidual(AutS, p);
    AutSp := ClosureGroup(AutSp, InnS);
    AutSp := PreImage(n, AutSp);

    return AutSp;
end);

InstallMethod(SemiCharacteristicSubgroups, "method for a p-group",
    [IsPGroup], function(S)
    local AutS, N;

    AutS := SemiAutomorphismGroup(S);
    N := SubgroupsSolvableGroup(S, rec(actions := GeneratorsOfGroup(AutS)));

    return N;
end);

InstallMethod(IsSemiCharacteristic, "method for p-group and subgroup",
    [IsPGroup, IsPGroup], function(S, P)
    local AutS;

    if HasSemiCharacteristicSubgroups(S) then 
        return P in SemiCharacteristicSubgroups(S);
    fi;
    
    AutS := SemiAutomorphismGroup(S);
    return ForAll(GeneratorsOfGroup(AutS), a -> Image(a, P) = P);    
end );

InstallMethod(SemiCharacteristicClosure, "method for p-group and subgroup", 
    [IsPGroup, IsPGroup], function(S,P)
    local semichars;

    if IsSemiCharacteristic(S, P) then return P; fi;

    semichars := SemiCharacteristicSubgroups(S);
    semichars := Filtered(semichars, A -> IsSubset(A, P));

    return Intersection(semichars);
end);
