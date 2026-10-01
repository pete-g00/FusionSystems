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

InstallMethod(RestrictedAutomorphism,  "method for restricting isomorphism to an automorphism", 
    [IsGroupHomomorphism and IsBijective, IsGroup], function(phi, T)
    local g, h;

    Assert(0, Image(phi,T) = T);
    
    g := GeneratorsOfGroup(T);
    h := List(g, x -> Image(phi,x));

    return GroupHomomorphismByImagesNC(T, T, g, h);
end );

InstallMethod(RestrictedAutomorphismSubgroup, "method for finding restricted automorphism subgroup", 
    [IsGroupOfAutomorphismsFiniteGroup, IsGroup and IsFinite], function(AutG, H)
    local g, h, AutH;

    g := GeneratorsOfGroup(AutG);
    h := List(g, phi -> RestrictedAutomorphism(phi, H));

    AutH := Group(h);
    
    SetIsGroupOfAutomorphismsFiniteGroup(AutH, true);
    SetAutomorphismDomain(AutH, H);

    return AutH;
end );

InstallMethod(RestrictedAutomorphismStabilizerSubgroup, "method for finding restricted automorphism subgroup", 
    [IsGroupOfAutomorphismsFiniteGroup, IsGroup and IsFinite], function(AutG, H)
    local n, AutG0;

    n := NiceMonomorphism(AutG);
    AutG := Image(n, AutG);

    AutG0 := Stabilizer(AutG, H, OnImageNM(n));
    AutG0 := PreImage(n, AutG0);

    return RestrictedAutomorphismSubgroup(AutG0, H);
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

# $\Aut_\calF(E)^g$ for some $g \in S$ and $E \leq S$
InstallOtherMethod(\^, "method to conjugate automorphism group by an element of an overgroup", 
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
    local S, gensA, gensP, N, a, x, cnj;
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

AutCommutatorSubgroup := function(A,P)
    local C, a, x, c;
    if not IsGroupOfAutomorphisms(A) then
        Error(A, "must be a group of automorphisms.");
    fi;
    if not IsSubgroup(AutomorphismDomain(A), P) then
        Error(A, "must act on a group of which", P, "is a subgroup");
    fi;
    if not IsInvariant(A,P) then
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
end;
