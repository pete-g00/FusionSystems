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
