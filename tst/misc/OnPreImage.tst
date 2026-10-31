# FusionSystems, MISC.gi, OnPreImage
#
gap> START_TEST("OnPreImage.tst"); 

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> AutS := AutomorphismGroup(S);;
gap> n := NiceMonomorphism(AutS);
<action isomorphism>
gap> AutS := n(AutS);;
gap> M := MaximalSubgroups(S);;
gap> Length(M);
4
gap> I := PositionsProperty(M, A -> Exponent(A) = 9);;
gap> Length(I);
2
gap> i := First([1..4], i -> not i in I);;
gap> Aut1 := AutomorphismGroup(M[I[1]]);;
gap> Aut2 := AutomorphismGroup(M[I[2]]);;
gap> x := RepresentativeAction(AutS, Aut1, Aut2, OnPreImage(n));;
gap> x <> fail;
true
gap> x := PreImagesRepresentative(n, x);;
gap> Aut1^x = Aut2;
true
gap> ForAll(GeneratorsOfGroup(S), a -> Aut1^a = Aut1);
true
gap> Aut3 := AutomorphismGroup(M[i]);;
gap> x := RepresentativeAction(AutS, Aut1, Aut3, OnPreImage(n));;
gap> x <> fail;
false
gap> ST := Stabilizer(AutS, [Aut1, Aut2], OnPreImageTuples(n));;
gap> Index(AutS, ST);
2
gap> ST = Stabilizer(AutS, M{I}, OnImageTuplesNM(n));
true

#
gap> STOP_TEST("OnPreImage.tst", 1);
