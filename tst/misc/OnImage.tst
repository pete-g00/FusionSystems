# FusionSystems, MISC.gi, OnImage
#
gap> START_TEST("OnImage.tst"); 

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> AutS := AutomorphismGroup(S);;
gap> M := MaximalSubgroups(S);;
gap> Length(M);
4
gap> O := Orbits(AutS, M, OnImage);;
gap> Length(O);
3
gap> AutS := SemiAutomorphismGroup(S);;
gap> M := MaximalSubgroups(S);;
gap> Length(M);
4
gap> O := Orbits(AutS, M, OnImage);;
gap> Length(O);
4

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> AutS := AutomorphismGroup(S);;
gap> M := MaximalSubgroups(S);;
gap> Length(M);
12
gap> O := Orbits(AutS, M, OnImage);;
gap> Length(O);
1
gap> AutS := SemiAutomorphismGroup(S);;
gap> M := MaximalSubgroups(S);;
gap> Length(M);
12
gap> O := Orbits(AutS, M, OnImage);;
gap> Length(O);
1

gap> S := SmallGroup(3^4, 7);
<pc group of size 81 with 4 generators>
gap> AutS := AutomorphismGroup(S);;
gap> n := NiceMonomorphism(AutS);
<action isomorphism>
gap> AutS := n(AutS);;
gap> M := MaximalSubgroups(S);;
gap> Length(M);
4
gap> O := Orbits(AutS, M, OnImageNM(n));;
gap> Length(O);
3
gap> AutS := SemiAutomorphismGroup(S);;
gap> AutS := n(AutS);;
gap> M := MaximalSubgroups(S);;
gap> Length(M);
4
gap> O := Orbits(AutS, M, OnImageNM(n));;
gap> Length(O);
4

gap> S := SmallGroup(11^3, 3);
<pc group of size 1331 with 3 generators>
gap> AutS := AutomorphismGroup(S);;
gap> n := NiceMonomorphism(AutS);
<action isomorphism>
gap> AutS := n(AutS);;
gap> M := MaximalSubgroups(S);;
gap> Length(M);
12
gap> O := Orbits(AutS, M, OnImageNM(n));;
gap> Length(O);
1
gap> AutS := SemiAutomorphismGroup(S);;
gap> AutS := n(AutS);;
gap> M := MaximalSubgroups(S);;
gap> Length(M);
12
gap> O := Orbits(AutS, M, OnImageNM(n));;
gap> Length(O);
1

#
gap> STOP_TEST("OnImage.tst", 1);
