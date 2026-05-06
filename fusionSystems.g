#Read("C:/Users/jxb1522/OneDrive - University of Birmingham/Birmingham/Maths/GAP/Fusion systems package/fusionSystems.g");


#Questions:

#How much information should I pass between functions?
#For instance, should I pass p (the prime of our p-groups) if it needs using, or should I recalculate it?
#Efficiency vs passing excessive number of arguments.

#I end up jumping between Aut and Out groups across different functions. Should I be consistent, and if so which should I use?

#What is standard practice for including checks and error messages in functions?

#Is the best way to have optional arguments to do function(x, y...)?



FindMinimumIntermediateSubgroupWithProperty:=function(Q, E, Prop, isNormal)

#Arguments:
#E is a group.
#Q is a normal subgroup of E.
#Prop is a group property satisfied by E.
#isNormal is a Boolean variable, true if we only want to check normal subgroups of E.

#Purpose and output:
#Returns a (normal if isNormal) subgroup between Q and E of minimal order satisfying Prop.

#Notes: there is IntermediateSubgroups(E,Q), but this ignores conjugacy so is presumably slower than looking at sbgps of E/Q.

	local phi, quotientSbgpClasses, quotSbgp, M;
	if Prop(Q)=true then	#Avoids enumerating subgroups.
		return Q;
	else
		phi:=NaturalHomomorphismByNormalSubgroup(E,Q);
		if isNormal then
			quotientSbgpClasses:=ShallowCopy(NormalSubgroups(phi(E)));	#List of normal sbgps of E/Q. #ShallowCopy needed to make list mutable.
		else
			quotientSbgpClasses:=List(ConjugacyClassesSubgroups(phi(E)), Representative);	#List of sbgps of E/Q up to conjugacy.
		fi;
		SortBy(quotientSbgpClasses, Order);	#Sorted by ascending order.
		for quotSbgp in quotientSbgpClasses do
			M:=PreImage(phi, quotSbgp);	#M is the corresponding subgroup between Q and E.
			if Prop(M) then
				return M;	#Returns the first M found satisfying Prop; since the list is sorted by order this has minimum order.
			fi;
		od;
	fi;
end;


CommutatorSubgroupOfGroupWithAuts:=function(E,A)

#Arguments:
#E is a group.
#A is a subgroup of Aut(E).

#Purpose and output:
#Returns the subgroup [E,A] of E.

#Notes: Still could be faster.

	#---Obselete: slow since A is often large (contains Inn(E))
	#local G, imA, imE;
	#G:=SemidirectProduct(A,E);	#We need to work in the semidirect product.
	#imA:=Image(Embedding(G,1));	#Embedding(G,1) gives the embedding A -> G. 
	#imE:=Image(Embedding(G,2));	#Embedding(G,2) gives the embedding E -> G.
	#return PreImage(Embedding(G,2), CommutatorSubgroup(imA,imE));	#Take the commutator and pull back to E.
	#---

	local gensE, gensA, commSbgpGens, e, a, b;
	gensE:=SmallGeneratingSet(E);
	gensA:=SmallGeneratingSet(A);
	commSbgpGens:=[];
	for e in gensE do
		for a in gensA do
			for b in gensA do	#Due to commutator product relations, we need to allow conjugates by A...
				Add( commSbgpGens, b(a(e)*(e^(-1))) );
			od;
		od;
	od;
	return NormalClosure(E, commSbgpGens);		#...and conjugates by E.

end;


MinimumIrreducibleHyperfocalNC:=function(E, A, p)

#Arguments:
#p is a prime.
#E is a p-group.
#A is a subgroup of Aut(E) containing Inn(E).

#Purpose and output:
#Returns a subgroup of minimum order [E,O^p(O^{p'}(A))]\leq Q\leq E which satisfies Q\cap\Phi(E)=\Phi(Q).

#Notes: function name may need changing as I haven't properly defined irreducibility in this context.

	local OpPrimeA, K, Q;
	OpPrimeA:=NormalClosure(A, SylowSubgroup(A,p));		#O^{p'}(A).

	#---Obselete
	K:=NormalClosure(A, Filtered(Elements(A), g -> Order(g) mod p <> 0) );		#K=O^p(A).
	#---

	#K:=Kernel(EpimorphismPGroup(OpPrimeA, p));	#K=O^p(OpPrimeA).	#This sometimes doesn't work??
	Q:=CommutatorSubgroupOfGroupWithAuts(E, K);	#Q=[E,K].

	#Find (normal) Q\leq M\leq E of minimum size which satisfies M\cap\Phi(E)=\Phi(M) and which A acts on.
	return FindMinimumIntermediateSubgroupWithProperty(Q, E, M -> Intersection(M,FrattiniSubgroup(E))=FrattiniSubgroup(M) and 
										ForAll(GeneratorsOfGroup(A), phi -> Image(phi, Q) = Q), true );

end;



MinimumIrreducibleHyperfocal:=function(E, A, p...)

#Previous function with checks.

	local pOfE;
	if not IsPGroup(E) then
		Print("Error. E is not a p-group for any p.");
	elif Length(p)>1 then
		Print("Error. MinimumIrreducibleHyperfocal takes at most 3 arguments.");
	else
		pOfE:=SmallestRootInt(Order(E));
		if Length(p)=1 then
			p:=p[1];
		else
			p:=pOfE;
		fi;
		if p<>pOfE then
			Print("Error. E is not a p-group.");
		elif not ( IsSubgroup(AutomorphismGroup(E), A) and IsSubgroup(A, InnerAutomorphismGroup(E)) ) then
			Print("Error. We must have Inn(E)\leq A\leq Aut(E).");
		else
			return MinimumIrreducibleHyperfocalNC(E, A, p);
		fi;
	fi;	
	
end;



SuccessiveCommutator:=function(E, Q, n)

#Arguments:
#E is a group.
#Q is a subgroup of E.
#n is a non-negative integer.

#Purpose and output:
#Returns the n-fold commutator [E,Q,...,Q], where we apply commutators from left to right.

	while n>0 do
		E:=CommutatorSubgroup(E,Q);
		n:=n-1;
	od;
	return E;

end;


CharInAnyExtn:=function(Q, S, isEssential)

#Arguments:
#Q is a p-group.
#S is a p-subgroup of Out(Q).
#isEssential is a Boolean variable, true if Q is an essential subgroup in some (unspecified) fusion system.

#Purpose and output:
#Attempts to check whether Q is characterstic in any extension of Q by S.

#Results used:
#1) Any rank 2 essential that is not a pearl is characteristic [Zhang 26+, not yet published].

#Notes: we shall eventually add more checks here.

	local charInAnyExtn, p;
	charInAnyExtn:=false;
	p:=SmallestRootInt(Order(Q));
	if Rank(Q)=2 and isEssential and Order(Q)>p^3 then	#Result 1.
		charInAnyExtn:=true;
	fi;
	return charInAnyExtn;

end;


OpPrime := function(G, p)

#Arguments:
#G is a group.
#p is a prime.

#Purpose and output:
#Returns O_{p'}(G).

   	local F, result, q;
    	result := TrivialSubgroup(G);
    	for q in PrimeDivisors(Order(G)) do
        	if q <> p then
            	result := ClosureSubgroup(result, PCore(G, q));		#O_{p'}(G) is the subgroup generated by all the q-cores for each q<>p.
        	fi;
    	od;
    	return result;

end;


IsSuzukiTwoGroup:=function(P)

#Arguments:
#P is a 2-group.

#Purpose and output:
#Returns true if P is a Suzuki 2-group.

	local centP;
	centP:=Centre(P);
	return centP=Omega(P,2) and centP=DerivedSubgroup(P) and centP=FrattiniSubgroup(P);

end;


ContainsStronglyPEmbeddedSubgroup:=function(A, p)

#Arguments:
#A is a group.
#p is a prime.

#Purpose and output:
#Returns a Boolean variable corresponding to whether A contains a strongly p-embedded subgroup.

#Results used:
#Classification of groups with an SpE sbgp.
#Groups with SpE sbgp have trivial p-core.

#Notes:
#Currently we use the classification of groups with SpE sbgps, which splits into an easy p-rank 1 case and...
#...a case where we have a list of possible almost simple groups M:=O^{p'}(A/O_{p'}(A)).

#Alternatively, we could take a Sylow p-sbgp S and take the closure of all normalisers N_A(Q) for Q\leq S.
#A has an SpE sbgp iff this closure is not equal to A.
#Is there any way it suffices to take the normalisers of only a small number of sbgps Q\leq S?

#We could use a hybrid method depending on the complexity of S.

#Questions: which method is fastest?

	local S, ordSExp, pPrimeQuot, M, simpleData, simpleFamily, n, q, name;

	if IsPrimePowerInt(Order(A)) or Order(A) mod p <> 0 then
		return false;		#Instantly reject if A has order a prime power, or not divisible by p.
	fi;

	S:=SylowSubgroup(A,p);

	if IsCyclic(S) or IsQuaternionGroup(S) then
		#return not IsNormal(A,Omega(S,p));	#This is the condition in the p-rank 1 case, but...
		return IsTrivial(PCore(A,p));	#...this is an equivalent condition which I think is faster.
		
	elif IsSolvableGroup(A) then	#A cannot be soluble in the p-rank >1 case.
		return false;

	#We are now in the p-rank >1 case.
	#The structure of S is quite limited, so we perform some cheap checks on S to reject some more cases.
	elif not IsElementaryAbelian(S) then
		if p=2 and not IsSuzukiTwoGroup(S) then
			return false;
		elif p=3 and not (Order(S)=27 and not IsAbelian(S)) then
			ordSExp:=Log(Order(S),3);
			if not (Exponent(S)=3 and ordSExp mod 3 = 0) or
				( ordSExp>=9 and ordSExp mod 6 = 3 and (not IsAbelian(S)) and IsTrivial(CommutatorSubgroup(S, DerivedSubgroup(S))) ) then
				return false;		#Assuming that Exponent(PSU_3(3^n)=3) for all n. True for n<=3.
			fi;
		elif not ( Log(Order(S),p) mod 3 = 0 and (not IsAbelian(S)) and IsTrivial(CommutatorSubgroup(S, DerivedSubgroup(S))) ) then
			return false;
		fi;
	fi;
	
	#A necessary condition for A to have an SpE sbgp is O_p(A)=1.
	if not IsTrivial(PCore(A,p)) then
		return false;

	else
		pPrimeQuot:=A/OpPrime(A, p);
		M:=NormalClosure(pPrimeQuot, SylowSubgroup(pPrimeQuot, p) );		#M:=O^{p'}(A/O_{p'}(A)).
		
		#If A has Spe sbgp, then M lies on a list of almost simple groups.
		if not IsSimpleGroup(M) then		#Only 2 possibilities that are almost simple but not simple.
			if p=3 and Order(M)=1512 then	#Necessary checks for M=PSL_2(8):C_3.
				return ForAny( MaximalSubgroupClassReps(M), H -> IdGroup(H)=IdGroup(PSL(2,8)) );
			elif p=5 and Order(M)=162688000 then	#The only non-soluble group with this order is Sz(32):C_5.
				return true;
			else
				return false;
			fi;

		else	#M is simple.
			simpleData:=IsomorphismTypeInfoFiniteSimpleGroup(M);
			simpleFamily:=simpleData.series;
			name:=simpleData.name;

			if simpleFamily="Spor" then		#Sporadics.
				return (name="M(11)" and p=3) or (name in ["Fi(22)", "McL"] and p=5) or (name="J4" and p=11);

			elif IsList(simpleData.parameter) then		#M has 2 parameters n,q (classical gps of Lie type).
				n:=simpleData.parameter[1];
				q:=simpleData.parameter[2];
				if SmallestRootInt(q)=p then
					return (n=2 and simpleFamily="L" and q<>p) or (n=3-1 and q<>2 and simpleFamily="2A");	#Note change of indexing for unitary groups.
				else
					return (n=3 and q=4 and p=3 and simpleFamily="L");
				fi;

			else	#M has a single parameter q (alternating groups and exceptional groups of Lie type).
				q:=simpleData.parameter;
				if simpleFamily="A" and (q=2*p or (q=5 and p=2) or (q=6 and p=3)) then
					#Covers A_{2p} and exceptional isoms to A_5=PSL_2(4) and A_6=PSL_2(9)
					return true;
				elif simpleFamily="2B" and p=2 then
					return true;
				elif simpleFamily="2G" and p=3 then
					return true;
				elif simpleFamily="2F" and p=3 and q=2 then
					return true;
				else
					return false;
				fi;
			fi;
		fi;
	fi;
end;


FixedPointsOfAction:=function(G, S)

#Arguments:
#G is a group acting (naturally) on the set S.

#Purpose and output:
#Returns the subset of S of fixed points under G.

#Questions:
#Surely there is a better / built-in way of doing this?

	return Union(Filtered(Orbits(G,S), x -> Length(x)=1));

end;


FixedSubspaceCodim:=function(G, V)

#Arguments:
#V is a finite elementary Abelian group.
#G is a subgroup of Aut(V)=GL(V), with V recognised as a vector space.

#Purpose and output:
#Let V_0 be the subspace of V (viewed as a vector space) fixed by G.
#Returns the codimension of V_0.

#Notes: It seems strange to pass V as an el Ab group rather than a vector space here, but this is because we will often have V=Q/Phi(Q) for some p-group Q.

	#---Obselete---
	#local F, d, V, fixedSubspace;
	#F:=FieldOfMatrixGroup(G);
	#d:=DimensionOfMatrixGroup(G);
	#V:=FullRowSpace(F,d);
	#---

	local p, fixedSubspace;
	p:=SmallestRootInt(Order(V));
	fixedSubspace:=FixedPointsOfAction(G,V);
	return Log(Order(V)/Length(fixedSubspace), p);

end;


HomToInducedActionModFrattini:=function(A, Q, fromOut...)

#Arguments:
#Q is a finite p-group.
#A is a subgroup of Aut(Q).
#fromOut is an optional Boolean variable telling us if we want the domain of the homomorphism to be A/Inn(Q) (rather than A).

#Purpose and output:
#Any automorphism of a finite p-group Q induces an action of the corresponding outer automorphism on Q/Frattini(Q).
#This function returns the homomorphism A/Inn(Q) -> Aut(Q/Frattini(Q)) induced by this action.

#Notes:
#We actually compute the induced homomorphism A -> Aut(Q/Frattini(Q)) first, before computing the induced homomorphism A/Inn(Q) -> Aut(Q/Frattini(Q)).
#Do we want to do this second bit oustide this function?

	local p, phiQ, phiA, AOut, QModFrat, homAToAutQModFrat, homOutAToActionOnQModFrat;
	p:=SmallestRootInt(Order(Q));
	phiQ:=NaturalHomomorphismByNormalSubgroup(Q, FrattiniSubgroup(Q));		#Q -> Q/Phi(Q)
	phiA:=NaturalHomomorphismByNormalSubgroup(A, InnerAutomorphismGroup(Q));		#A -> A/Inn(Q)
	AOut:=phiA(A);		#A/Inn(Q)
	QModFrat:=phiQ(Q);		#Q/Phi(Q)
	
	#Induce action of A on Q to action of A on Q/Phi(Q).
	homAToAutQModFrat:=GroupHomomorphismByFunction(A, AutomorphismGroup(QModFrat), a -> InducedAutomorphism(phiQ, a));

	if Length(fromOut)<>1 or not fromOut[1] then
		return homAToAutQModFrat;
	else

		#Induce action of A on Q/Phi(Q) to action of A/Inn(Q) on Q/Phi(Q).
		homOutAToActionOnQModFrat:=GroupHomomorphismByFunction(AOut, AutomorphismGroup(QModFrat), x -> ImageElm(homAToAutQModFrat, PreImagesRepresentative(phiA, x)));

		return homOutAToActionOnQModFrat;
	fi;

end;


TwoPearlParentStaysInEParent:=function(Q, E)

#Arguments:
#E is a 2-group.
#Q is a subgroup of E isomorphic to a pearl (C_p x C_p or p^{1+2}_+ for p odd or Q_8).

#Purpose and output:
#Suppose that E is a self-centralising subgroup in a fusion system on a 2-group P.
#Suppose that E is Q-hyperfocused (and that Q is isomorphic to a pearl).
#Then we apply theory to determine information about the structure of P.
#Returns a Boolean variable QParentsCanStayInE.
#This is true if we cannot rule out the existence of a map theta in Aut_P(N_P(E_j)) such that theta(E_j)\neq E_j and theta(Q_{(j)})\leq E_j, where E_j is the jth normaliser of E in P and Q_{(j)}\leq E_j is a certain normal subgroup of the same type as Q (quat or dih).

#Results used:
#Theorem [TBC] of mine.

	local p, QParentsCanStayInE, m, agemoDerivedR, R, pi, widerR;
	p:=SmallestRootInt(Order(Q));
	QParentsCanStayInE:=false;
	R:=E/Q;
	if not IsAbelian(R) then	#R must be non-Abelian.
		if Order(Q)=p^2 then	#We must have E=Q x E/Q.
			#We search R for sbgps X which are normal in E, dihedral or V_4, and satisfy [X,R]\nleq\Phi(X).
			QParentsCanStayInE:=ForAny(NormalSubgroups(R), X -> IsNormal(E, X) and Order(X)>=4 and IsDihedralGroup(X) and not IsSubset(FrattiniSubgroup(X), CommutatorSubgroup(X,R)));

		else
			R:=Centraliser(E,Q);
			#Get minimum m for which Z(Q)\nleq Agemo_m(R').
			m:=0;
			agemoDerivedR:=DerivedSubgroup(R);
			while IsSubset(agemoDerivedR, Centre(Q)) do
				agemoDerivedR:=Agemo(agemoDerivedR, 2);
				m:=m+1;
			od;

			#We test if Q_j embeds in the second centraliser in E_j of Q_j.
			pi:=NaturalHomomorphismByNormalSubgroup(E,Centre(Q));
			widerR:=ClosureSubgroup(R, MaximalSubgroups(Q)[1]);		#C_4\circ R where C_4 is some maximal sbgp of Q=Q_8. This is the second centraliser in E_j of Q_j.

			#We search R for sbgps X which are normal in E, quaternion, satisfy [X,R]\nleq\Phi(X), and if Z(Q)\nleq mho_m(R') then X\leq R.
			QParentsCanStayInE:=ForAny(NormalSubgroups(widerR), X -> IsNormal(E, X) and IsQuaternionGroup(X) and not IsSubset(FrattiniSubgroup(X), CommutatorSubgroup(X,widerR)) and (Order(X)<p^(m+3) or IsSubset(R, X)) );
		fi;
	fi;
	return QParentsCanStayInE;
end;


SbgpsSatisfyingCodimInequality:=function(Q, S, p, isEssential...)

#Arguments:
#p is a prime.
#Q is a p-group.
#S is a p-subgroup of Aut(Q).
#isEssential is a Boolean variable, true if Q is an essential subgroup.

#Purpose and output:
#Returns a list of 2-tuples.
#The first element runs over all elementary Abelian subgroups B\leq S/Inn(Q) satisfying codim(C_{Q/Phi(Q)}(B))\leq\dim(B).
#The second element is the non-negative integer codim(C_{Q/Phi(Q)}(B)).

#Questions:
#

	local pi, SOutAsQModFratAuts, satisfyingCodimInequality, B, fixedSubspaceCodim;
	pi:=NaturalHomomorphismByNormalSubgroup(S, InnerAutomorphismGroup(Q));
	SOutAsQModFratAuts:=(HomToInducedActionModFrattini(S, Q))(S);	#Consider S\leq\Aut(Q/Phi(Q)).
	
	satisfyingCodimInequality:=[];
	for B in Filtered(AllSubgroups(LatticeByCyclicExtension(SOutAsQModFratAuts, IsElementaryAbelian)), B -> not IsTrivial(B)) do
		fixedSubspaceCodim:=FixedSubspaceCodim(B, Q/FrattiniSubgroup(Q));
		if fixedSubspaceCodim <= Log(Order(B), p) then
			Add(satisfyingCodimInequality, [B, fixedSubspaceCodim]);
		fi;
	od;
	return satisfyingCodimInequality;
end;


ImagesOfQInE:=function(Q, E, S)

#Arguments:
#E is a p-group.
#Q is a p-subgroup of E.
#S is a p-subgroup of Aut(E) containing Inn(E).
#

#Purpose and output:
#Returns a list of all possible images of Q in E under a map from Aut_P(N).

	local T, possibleSubs;
	possibleSubs:=Filtered(NormalSubgroups(E), T -> IsomorphismGroups(Q, T)<>fail );	#Normal in E and isomorphic to Q.
	possibleSubs:=Filtered(possibleSubs, T -> Length(Orbit(S, AsSet(T), OnSets))=1);	#Normalised by S.
	possibleSubs:=Filtered( possibleSubs, T -> IsomorphismGroups( CommutatorSubgroupOfGroupWithAuts(Q, S), CommutatorSubgroupOfGroupWithAuts(T, S) )<>fail );
	possibleSubs:=Filtered(possibleSubs, T -> CommutatorSubgroup(T,E)<>FrattiniSubgroup(T));
	return possibleSubs;

end;


CheckPhiQCanLeavePhiE:=function(Q, E, IsElemAb)

	if IsElementaryAbelian(Q) then
		return false;
	elif Q=E and IsElemAb and Length( Filtered( NormalSubgroups(E), X -> Order(X)=Order(FrattiniSubgroup(Q)) and
						IdGroup(X)=IdGroup(FrattiniSubgroup(Q)) ) )=1 then
		return false;	#No other normal sbgp of E is isomorphic to Phi(E), and N/E is elementary Abelian.
	else
		return true;
	fi;

end;


FrattiniCharInNormaliserCheck:=function(Q, E, S, QImageIntersectEIsInQ, frattiniQUniquelyNormalInQ)

#Arguments:
#E a p-group.
#Q a subgroup of E.
#extBy is a p-group.
#Let N be an extension of E by S, and let \theta\in\Aut(N) be a p-automorphism.
#Then QImageIntersectEIsInQ is a Boolean variable for whether E\cap\theta(Q)\leq Q.
#frattiniQUniquelyNormalInQ is a Boolean variable for whether \Phi(Q) is the unique normal subgroup of Q isomorphic to \Phi(Q).

#Purpose and output:
#Given p-groups Q\leq E and S, performs checks as to whether \Phi(E) is characteristic in any extension of E by S.
#Returns true if these checks yield an affirmative answer.
#Returns false if it cannot determine whether the answer is yes or no.

#Current sufficient conditions implementable:
#Q is elementary Abelian.
#S is elementary Abelian, and (QImageIntersectEIsInQ and frattiniQUniquelyNormalInQ)=true.
#\Phi(E)=Z(E) and either
#this is of order p, or
#any automorphism of E acts trivially on Z(E).

end;


PossibleAutFE:=function(E, onlyOpPrime...)

#Arguments:
#E is a p-group.

#Purpose and output:
#Computes all possible subgroups of Aut(E) which appear as Aut_F(E) for some fusion system F with an essential subgroup E.
#Returns the list of all such subgroups up to Aut(E)-conjugacy.

#Questions:
#Given G with a p-subgroup S, how easy is it to compute all subgroups of G with S as their Sylow p-subgroup?
#If this is feasible, we could enumerate sbgps of S up to conjugacy, filter to permissible S, and then look for all subgroups of G containing one of these S as a Sylow p-subgroup.
#Would this be quicker?

	local p, gpsToCheck, possibleOutFE, pi, OutGp, m, d, A, hom, twoValuation, G, possibleOutFEModOp, possibleOutFEProdOp, AK, comps, K,
		homToActionModFrattini, outGpAsFaithfulAction, OpOutGp, modOp, outGpModOp, possibleAutFE;

	if not IsPrimePowerInt(Order(E)) then	#Sanity check.
		Print("Error, the argument must be a non-trivial p-group.");
		return fail;
	else
		p:=SmallestRootInt(Order(E));
	fi;

	gpsToCheck:=[];
	possibleOutFE:=[];
	A:=AutomorphismGroup(E);
	if IsPrimePowerInt(Order(A)) then	#If Aut(E) is a p-group then no possible Aut_F(E) exist for E essential.
		return possibleOutFE;
	fi;

	pi:=NaturalHomomorphismByNormalSubgroup(A, InnerAutomorphismGroup(E));
	OutGp:=pi(A);	#Out(E)
	OpOutGp:=PCore(OutGp, p);	#O_p(Out(E))
	modOp:=NaturalHomomorphismByNormalSubgroup(OutGp, OpOutGp);
	outGpModOp:=modOp(OutGp);	#Out(E)/O_p(Out(E))
	#We can work mod O_p(Out(E)) as any possible Out_F(E) intersects this trivially.
	#This means less supbgroups to enumerate.
	
	#---Obselete
	#Limitations:
	#Computing Out(E) is a difficult problem when rank(E) is large.
	#A list of possible isomorphism types of Out_F(E) exists or is easily obtainable in the following cases:
	#rank(E)=2,
	#p=2 and rank(E)\leq 5,
	#p=3 and rank(E)\leq 3.
	#Let G:=Out_F(E). Outside these cases, we only know that either G has p-rank 1, or that O^{p'}(G/O_{p'}(G)) is on a given list.
	#Even when we have a list of isomorphism types to check, if Out(E) is large then finding subgroups with these isomorphism types is a difficult problem.

	#Current methods:
	#We first perform sanity checks that the order of a possible Out_F(E) divides the order of Out(E).
	#If we have a list of possible isomorphism types of Out_F(E), then we just search for subgroups of Out(E) with these types.
	# if not IsCyclic(E) then
	# 	pi:=NaturalHomomorphismByNormalSubgroup(AutomorphismGroup(E), InnerAutomorphismGroup(E));
	# 	OutGp:=pi(AutomorphismGroup(E));
	# 	m:=Order(OutGp)/(p^Valuation(Order(OutGp),p));		#The p'-part of the order of Out(E).
	# 	if m<>1 then
	# 		d:=Rank(E);
	# 		if p=2 then
	# 			if m mod 3 = 0 then
	# 				Add(gpsToCheck,SymmetricGroup(3));
	# 			fi;
	# 			if d>3 then
	# 				if m mod 5 = 0 then
	# 					Append(gpsToCheck,[DihedralGroup(10), SmallGroup(20,3), SmallGroup(60,7)]);
	# 					if m mod 3 = 0 then
	# 						Append(gpsToCheck,[DirectProduct(DihedralGroup(10),CyclicGroup(3)), AlternatingGroup(5)]);
	# 						if m mod 9=0 then
	# 							Add(gpsToCheck,GL(2,4));
	# 						fi;
	# 					fi;
	# 				elif m mod 9 = 0 then
	# 					Append(gpsToCheck,[DirectProduct(SymmetricGroup(3),CyclicGroup(3)), SmallGroup(18,4), SmallGroup(36,9)]);
	# 				fi;
	# 			fi;
	# 			if d>4 and m mod 7 = 0 then
	# 				Append(gpsToCheck, [DirectProduct(SymmetricGroup(3),CyclicGroup(7))]);
	# 				if m mod 9 = 0 then
	# 					Append(gpsToCheck, [DirectProduct(SymmetricGroup(3),SmallGroup(21,1))]);
	# 				fi;
	# 			fi;
	# 		elif p=3 and d<=3 then
	# 			twoValuation:=Valuation(m, 2);
	# 			if twoValuation>=3 then
	# 				Add(gpsToCheck, SL(2,3));
	# 				if twoValuation>=4 then
	# 					Add(gpsToCheck, GL(2,3));
	# 				fi;
	# 			fi;
	# 			if d=3 then
	# 				if m mod 13 = 0 then
	# 					Add(gpsToCheck, SmallGroup(39,1));
	# 					if twoValuation>=1 then
	# 						Add(gpsToCheck, DirectProduct(SmallGroup(39,1), CyclicGroup(2)));
	# 					fi;
	# 				fi;
	# 			fi;
	# 			if twoValuation>=2 then
	# 				Add(gpsToCheck, AlternatingGroup(4));
	# 				if twoValuation>=3 then
	# 					Append(gpsToCheck, [SymmetricGroup(4), DirectProduct(AlternatingGroup(4), CyclicGroup(2))]);
	# 					if twoValuation>=4 then
	# 						Append(gpsToCheck, [DirectProduct(SL(2,3), CyclicGroup(2)), DirectProduct(SymmetricGroup(4), CyclicGroup(2))]);
	# 						if twoValuation>=5 then
	# 							Add(gpsToCheck, DirectProduct(GL(2,3), CyclicGroup(2)));
	# 						fi;
	# 					fi;
	# 				fi;
	# 			fi;
	# 		elif d=2 and m mod p^2-1 then
	# 			Add(gpsToCheck, SL(2,p));
	# 		fi;
	# 	fi;
	# fi;
	#---

	#Enumerate sgps of Out(E)/O_p(Out(E)) up to conjugacy.
	possibleOutFEModOp:=List(ConjugacyClassesSubgroups(outGpModOp), Representative);
	#Use our function to test for SpE sbgp.
	possibleOutFEModOp:=Filtered(possibleOutFEModOp, X -> ContainsStronglyPEmbeddedSubgroup(X,p));
	if Length(onlyOpPrime)=1 and onlyOpPrime[1] then
		possibleOutFEModOp:=Filtered(possibleOutFEModOp, X -> X=NormalClosure(X, SylowSubgroup(X,p)));
	fi;
	
	possibleOutFEProdOp:=List(possibleOutFEModOp, X -> PreImage(modOp, X));
	possibleOutFE:=[];
	#We need to check if each SpE sbgp of Out(E)/O_p(Out(E)) lifts to a complement.
	for AK in possibleOutFEProdOp do
		comps:=ComplementClassesRepresentatives(AK, OpOutGp);
		if Length(comps)>0 then
			Append(possibleOutFE,[comps[1]]);# List(comps, X -> X^OutGp));
		fi;
	od;

	#Print(Runtime(),"\n");

	#possibleOutFE:=Filtered(List(ConjugacyClassesSubgroups(OutGp), Representative), X -> Order(X) in List(gpsToCheck, Order));
	#possibleOutFE:=Filtered(possibleOutFE, X -> IdGroup(X) in List(gpsToCheck, IdGroup));
	#for G in gpsToCheck do
	#	Append(possibleOutFE, List(Filtered(AllHomomorphismClasses(G,OutGp), hom -> IsInjective(hom)) , alpha -> alpha(G)) );
	#od;

	possibleAutFE:=List(Set(possibleOutFE), X -> PreImage(pi, X));	#Return the preimages in Aut(E).
	return possibleAutFE;
	#return Set(List(possibleAutFE, X -> ConjugacyClass(A, X)));

end;

#ExponentsAutPGroup

#Example test - takes ~20 secs.
#List(AllSmallGroups(Size, [4,8,16,32,64], RankPGroup, [1..4]), PossibleAutFE);;


FrattiniQuotientYieldsSubspace:=function(E, Q)

#Arguments:
#E is a p-group.
#Q is a subgroup of E.

#Purpose and output:
#Returns the Boolean value for Q\cap\Phi(E)=\Phi(Q).

end;



StructureForcedByCentRadSbgp:=function(E, A)

#Arguments:
#E is a p-group.
#A is a subgroup of Aut(E) containing Inn(E), for which O_p(A)\leq\Inn(E).

#Purpose and output:
#Let F be a fusion system on a p-group P, where E<P is a self-centralising radical subgroup and A=Aut_F(E).
#Performs checks to try to determine the structure of P.
#Returns the following list of data:
#[essentialCharacteristic, minimalHyperfocal, normaliserTowerHeight].
#essentialCharacteristic is a Boolean variable which is true if for any such F, we have E characteristic in P.
#minimalHyperfocal is a normal subgroup of E; the minimal subgroup Q of E for which E is Q-hyperfocused with respect to Out(E).
#normaliserTowerHeight is a positive integer which measures the height of the normaliser tower of E in P.

#Methods:

	local p, AOut, Q, PHasMaximalClass, QCanStayInE, isRadical, isEssential, QCanLeaveEWithoutPhi, S, SOut, SAsQAuts, SOutAsQModFratAuts,
		codimInequalityHolds, PhiQCanLeavePhiE, QMaximalClass, QMaximalClassData, satisfyingCodimInequality, QParentsCanStayInE, t1, t2, t3, t4, t5, t6, t7, t8;
	t1:=Runtime();
	p:=SmallestRootInt(Order(E));
	AOut:=A/InnerAutomorphismGroup(E);

	isRadical:=(IsTrivial(PCore(AOut,p)));	#Check that E is indeed F-radical.
	if not isRadical then
		Print("Error: E is not F-radical. Please try a different A.");
	fi;

	S:=SylowSubgroup(A,p);
	satisfyingCodimInequality:=SbgpsSatisfyingCodimInequality(E, S, p);
	t2:=Runtime();

	QCanLeaveEWithoutPhi:=true;
	if Length(satisfyingCodimInequality)=0 then
		QCanLeaveEWithoutPhi:=false;
	fi;

	Q:=MinimumIrreducibleHyperfocalNC(E, A, p);	#Use result to choose Q.

	t3:=Runtime();
	QMaximalClass:=false;
	if (Order(Q)=p^2 and IsElementaryAbelian(Q)) or (Order(Q)=p^3 and not IsAbelian(Q) and (IsQuaternionGroup(Q) or Exponent(Q)=p)) then	#Check if Q is a pearl.
		QMaximalClass:=true;
		PHasMaximalClass:=false;
		if Q=E then
			PHasMaximalClass:=true;		#Elementary result: self-centralising maximal class subgroup implies maximal class.
			QParentsCanStayInE:=false;
		elif p=2 then
			QParentsCanStayInE:=TwoPearlParentStaysInEParent(Q, E);		#Apply theory for when Q is isomorphic to a 2-pearl.
		fi;
		t4:=Runtime();
		return [Q, QMaximalClass, PHasMaximalClass, QCanLeaveEWithoutPhi, QParentsCanStayInE];

	else
		isEssential:=ContainsStronglyPEmbeddedSubgroup(AOut,p);		#We can use more powerful results if E is essential (currently only for p=2).
		t4:=Runtime();
		SOut:=SylowSubgroup(AOut,p);

		if Length(satisfyingCodimInequality)=1 and Order(satisfyingCodimInequality[1][1])=Order(SOut) then	#Check if only S satisfies the inequality.
			if CharInAnyExtn(Q, S, isEssential) then	#We check the hypotheses for our result about p-groups characteristic in extensions.
				if (isEssential and p=2 and Rank(Q)=2*Rank(SOut)) or
				( Rank(Q)=Rank(SOut)+Rank( CommutatorSubgroupOfGroupWithAuts(Q, S)/FrattiniSubgroup(Q) ) ) then
					QCanLeaveEWithoutPhi:=false;
				fi;
			fi;
		fi;			

			#SAsQAuts:=Image(GroupHomomorphismByFunction(S, AutomorphismGroup(Q), a -> RestrictedMapping(a, Q)));
			#t5:=Runtime();
		
			#if isEssential and p=2 then
			#	if IsElementaryAbelian(SOut) and FixedSubspaceCodim(InducedActionModFrattini(S, Q), Q/FrattiniSubgroup(Q)) <= Log(Order(SOut), p) then
			#		satisfyingCodimInequality:=[SOut];
			#	else
			#		satisfyingCodimInequality:=[];
			#	fi;
			#else
		
			#satisfyingCodimInequality:=SbgpsSatisfyingCodimInequality(Q, SAsQAuts, p);	#Check which B\leq S satisfy codim(C_{Q/Phi(Q)}(B)\leq\dim(B).
			t6:=Runtime();		

			#return satisfyingCodimInequality;
			#fi;

			

		if Q=E then
			QCanStayInE:=false;
		else
			QCanStayInE:=(Length(ImagesOfQInE(Q, E, S))>1);		#Check if E contains another subgroup isomorphic to Q satisfying the required conditions.
		fi;

		PhiQCanLeavePhiE:=CheckPhiQCanLeavePhiE( Q,E,IsElementaryAbelian(SylowSubgroup(A,p)) );

	fi;

	return [Q, QMaximalClass, QCanStayInE, QCanLeaveEWithoutPhi, PhiQCanLeavePhiE];		#, t1, t2, t3, t4, t5, t6, t7, t8];

end;


SummariseData:=function(E, Q, QMaximalClass, PHasMaximalClass, QCanStayInE, QCanLeaveEWithoutPhi, PhiQCanLeavePhiE)

#Arguments:
#E is a p-group.
#Q is a normal subgroup of E which admits a p'-automorphism.
#The remaining arguments are Boolean.

#Purpose and output:
#The function StructureForcedBySbgp obtains data about a fusion system in which E is self-centralising.
#SummariseData provides a printed description of what this data tells is about the structure of the fusion system.

	local QQuaternion, QType, TextEQuatOrDih, TextEMaxlClassOdd, TextProperQQuatOrDih, TextENormal, TextQStaysInE, TextPhiQLeavesPhiE,
		TextNoInfo, p;
	QQuaternion:=true;
	QType:="";
	TextEQuatOrDih:=Concatenation("P is ", QType, " or semidihedral.\n");
	TextEMaxlClassOdd:="P has maximal class.\n";
	TextProperQQuatOrDih:=Concatenation("E has maximal normaliser tower in P.\n", "P has a maximal subgroup of the form TR, where T is ",
						QType, " and has 2 maximal subgroups P-conjugate.\n",
						"Moreover [T,R] is contained in gamma_j(T).\n");
	TextENormal:="E is normal in P.\n";
	TextQStaysInE:="There exists a map theta in Aut_P(N) for which theta(E)\neq E and theta(Q)\leq E.\n";
	TextPhiQLeavesPhiE:="There exists a map theta in Aut_P(N) for which theta(E)\neq E and theta(Phi(Q))\nleq\Phi(E).\n";
	TextNoInfo:="No further information about the structure of P has been obtained.\n";
	if not (QCanStayInE or QCanLeaveEWithoutPhi or PhiQCanLeavePhiE) then
		Print(TextENormal);
	elif QMaximalClass then
		p:=SmallestRootInt(Order(Q));
		if p=2 then
			if IsQuaternion(Q) then
				QType:="quaternion";
			elif IsDihedralGroup(Q) then	#Q is dihedral or V_4.
				QType:="dihedral";
			fi;
			if QType<>"" then
				if Q=E then
					Print(TextEQuatOrDih);
				else
					if QCanStayInE then
						Print("There are two possible options.\n");
						Print("Option 1:\n");
						Print(TextProperQQuatOrDih);
						Print("Option 2:\n");
						Print(TextQStaysInE);
					else
						Print(TextProperQQuatOrDih);
					fi;
				fi;
			fi;
		elif Q=E then
			Print(TextEMaxlClassOdd);
		else
			Print(TextNoInfo);
		fi;
	elif QCanLeaveEWithoutPhi then
		Print(TextNoInfo);
	elif QCanStayInE and (not PhiQCanLeavePhiE) then
		Print(TextQStaysInE);
		Print("Any choice of map has this property.\n");
	elif (not QCanStayInE) and PhiQCanLeavePhiE then
		Print(TextPhiQLeavesPhiE);
		Print("Any choice of map has this property.\n");
	elif QCanStayInE and PhiQCanLeavePhiE then
		Print("There are two possible options.\n");
		Print("Option 1:\n");
		Print(TextQStaysInE);
		Print("Option 2:\n");
		Print(TextPhiQLeavesPhiE);
	fi;
end;


#Options:
#Q=E quaternion or dihedral.
#Q=E maximal class for p odd.
#Q\neq E quaternion or dihedral
	#QCanStayInE=true
#E must be normal in P.
#Must have theta(Q)\leq E.
#theta(Q)\nleq E requires theta^t(Phi(Q))\nleq Phi(E) for some t.


getAllEssentialsNotNormalOrPearlHyperfocused:=function(p, n)

	local interestingList, interestingA, i, ess, A, strucData, essIsom;
	interestingList:=[];
	for i in [2..n] do
		for ess in AllSmallGroups(p^i) do
			interestingA:=[];
			for A in PossibleAutFE(ess) do
				strucData:=StructureForcedByCentRadSbgp(ess, A);
				#if (strucData[2] and p=2 and strucData[5]) or (not strucData[2] and (strucData[3] or strucData[4] or strucData[5])) then
				#	Add(interestingA, [StructureDescription(strucData[1]), StructureDescription(A/InnerAutomorphismGroup(ess)), strucData{[2..5]}]);
				#fi;

				#Selecting non-pearl-hyperfocused for which something satisfies the codim inequality:
				if not strucData[2] and strucData[4] then
					Add(interestingA, [ StructureDescription(strucData[1]), StructureDescription(A/InnerAutomorphismGroup(ess)) ]);
				fi;
			od;
			if Length(interestingA)>0 then
				Print(StructureDescription(ess), ", ",IdGroup(ess), ": ");
				Print(interestingA,"\n");
				#essIsom:=[StructureDescription(ess)];
				#Add(essIsom, interestingA);
				#Add(interestingList, essIsom);
			fi;
		od;
	od;
	return interestingList;
end;


charnessOfHyperfocalInduces:=function(E, Q)

#Arguments:
#E is a p-group.
#Q is a subgroup of E.

#Output and purpose:
#Suppose that whenever Q appears as essential in some fusion system on P, it must be characteristic in P.
#Performs checks as to whether this property holds for E, assuming that any P-automorphism \theta of N:=N_P(E) which satisfies \theta(Q)\leq E must be inner.
#Returns a Boolean variable which is true if the above property for E holds.


end;
