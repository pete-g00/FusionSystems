# SU type
gap> G := SemidirectProduct(SU(3,3), GF(9)^3);;
gap> P := SylowSubgroup(G, 3);; iso := IsomorphismPcGroup(P);; S := Image(iso);;
gap> Ex := Image(iso, Intersection(P, Image(Embedding(G, 2))));;
gap> IsPGroup(S);; IsPGroup(Ex);;
gap> IdGroup(S/Ex);
[ 27, 3 ]
gap> SPESylowType(Normalizer(S, Ex)/Ex, Rank(Ex));
2
gap> IsProtoEssential(S, Ex);
true
