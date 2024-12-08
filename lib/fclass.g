FClassCons := function(G, f, A, R)
    # return a construction
end;

FClass := function(F, A)
    # construct by using FClassCons
end;

Representative := function(C)
    return C!.A;
end;

# returns all Aut_F(S)-reps of a class
Reps := function(C)
    return C!.subs;
end;

Size := function(C)
    n := 0;
    f := C!.f;
    G := C!.G;

    for T in Reps(C) do 
        n := n + Size(Image(f,T)^G);
    od;

    return n;
end;

\in := function(A, C)
    f := C!.f;
    G := C!.G;

    return ForAny(Reps(C), T -> Image(f,A) in Image(f,T)^G);
end;

# find a way to iterate through the elements

FindMap := function(C, B)
    A := C!.A;
    f := C!.f;
    s := Reps(C);
    m := C!.maps;

    for i in [1..Length(s)] do 
        T := s[i];
        if Image(f,B) in Image(f,T)^G then 
            x := RepresentativeAction(G,Image(f,B),Image(f,T));
            x := ConjugatorIsomorphism(Image(f,B),x);
            x := OnHomConjugation(x, f);
            return m[i]*x;
        fi;
    od;

    return fail;
end;
