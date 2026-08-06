/*
PolycirculantCounterexample
Authors: Saul D. Freedman and Melissa Lee.

Magma code that verifies the computational claims in the paper "An infinite family of counterexamples to the Polycirculant Conjecture" by Saul D. Freedman and Melissa Lee.

To run, execute the command PolycirculantCounterexample().
Set the overgroups parameter to false to verify only Computational Propositions 4.1 and 4.2;
or the graphs parameter to false to verify only Computational Propositions 4.1, 4.3 and 4.4.

Approximate computational requirements: 35 minutes (with a 3.85 GHz processor) and 15 GB of RAM.
If overgroups is set to false, 13 minutes and 0.8 GB of RAM are required.
If graph is set to false, 25 minutes and 15 GB of RAM are required.

Last updated: 25 July 2026.
*/

procedure PolycirculantCounterexample(:graph:=true,overgroups:=true)

	error if not (graph or overgroups), "At least one of the parameters graph and overgroups must be true.";

	"Constructing a group Xabs that is abstractly isomorphic to X.";

	G:=PSU(3,3);
	I:=IrreducibleModules(G,GF(7));
	Ns:=[i:i in I|Dimension(i) eq 6];
	assert #Ns eq 1; // There is a unique irreducible 6-dimensional G-module over GF(7).
	N:=Ns[1];
	Hs:=Subgroups(G:OrderEqual:=18);
	assert #Hs eq 1; // There is a unique conjugacy class of subgroups of G of order 18.
	H:=Hs[1]`subgroup;
	CM:=CohomologyModule(G,N);
	H2:=CohomologyGroup(CM,2);
	MG:=MaximalSubgroups(G);
	assert Dimension(H2) eq 1 and #DistinctExtensions(CM) eq 2; // There is only one non-split extension N.G (and one split extension).
	Xabs,a,b:=Extension(GrpPerm,CM,H2.1:UseSubgp:=true,Subgp:=MG[1]`subgroup); // Using the UseSubgp and Subgp parameters results in a faster computation.
	assert not HasComplement(Xabs,Image(b)); // The constructed extension N.G is non-split.

	"Constructing the subgroup Y of Xabs.";
	// There are two possible subgroups Y, up to conjugacy; which one is chosen does not affect the assertions below.

	L:=H@@a;
	SL:=Subgroups(L:OrderMultipleOf:=#H);
	_:=exists(Y){i`subgroup:i in SL|i`order eq 43218 and #NormalSubgroups(i`subgroup) eq 16};

	"Constructing the permutation group X of degree 16464 and checking that it is elusive.";

	X:=CosetImage(Xabs,Y);
	assert not exists{i:i in Classes(X)|IsPrime(i[1]) and #Fix(i[3]) eq 0};

	"Constructing Delta, XSigma and XDelta.";
	// Delta is a block in the X-invariant partition Sigma, XSigma is the permutation group
	// induced on Sigma by X, and XDelta is the permutation induced on Delta by Stab, the
	// stabiliser of Delta in X.

	AP:=AllPartitions(X);
	_:=exists(Delta){i:i in AP|#i eq 294};
	s,XSigma:=BlocksAction(X,Delta);
	Stab:=Stabiliser(X,Delta);
	d,XDelta:=Action(Stab,GSet(Stab,Delta));

	"Constructing the 2-closure XSigma2 of XSigma.";

	SymXSigma:=SymmetricGroup(Support(XSigma));
	PXSigma:=MinimalPartition(XSigma);
	XSigma2:=Stabiliser(SymXSigma,PXSigma);
	while exists(o){i[2]:i in OrbitRepresentatives(Stabiliser(XSigma2,1))|#Orbit(Stabiliser(XSigma,1),i[2]) ne i[1]} do
		GS:=GSet(XSigma2,{[1,o]});
		mu,Q:=Action(XSigma2,GS);
		Orbs:=Orbits(XSigma@mu);
		XSigma2:=Stabiliser(Q,Orbs)@@mu;
	end while;

	if overgroups then
	
		"Showing that XDelta is 2-closed.";
		// Alternatively, we can use the TwoClosure function in GAP, which is significantly faster.
		// If we are only looking for a vertex-transitive graph with automorphism group X, we do not need this to be verified.

		SymXDelta:=SymmetricGroup(Support(XDelta));
		PXDelta:=MinimalPartition(XDelta);
		XDelta2:=Stabiliser(SymXDelta,PXDelta);
		while exists(o){i[2]:i in OrbitRepresentatives(Stabiliser(XDelta2,1))|#Orbit(Stabiliser(XDelta,1),i[2]) ne i[1]} do
			GS:=GSet(XDelta2,{[1,o]});
			GSXDelta:=GSet(XDelta,GS); // These extra lines of code are necessary as XDelta is not actually a subgroup of XDelta2.
			muXDelta,QXDelta:=Action(XDelta,GSXDelta);
			Orbs:=Orbits(QXDelta);
			mu,Q:=Action(XDelta2,GS);
			XDelta2:=Stabiliser(Q,Orbs)@@mu;
		end while;

		assert #XDelta2 eq #XDelta;
		
	end if;

	"Constructing W = (2-closure of XDelta) wr (2-closure of XSigma) = XDelta wr XSigma2.";

	W,ph,th:=WreathProduct(XDelta,XSigma2);

	"Constructing the embedding of X in W.";
	// We use the embedding described in Alexander Hulpke's lecture notes "Notes on Computational Group Theory" (2010).

	Reps:=[];
	for i in [1..Degree(XSigma)] do
		_,r:=IsConjugate(XSigma,1,i);
		Append(~Reps,r@@s);
	end for;
	
	function homembed(x)

		elt:=(x@s)@th;
		for j in [1..#Reps] do
			elt:=elt*((Reps[j^((x^-1)@s)]*x*Reps[j]^-1)@d)@ph[j];
		end for;
		
		return elt;
	
	end function;	

	Gens:=[homembed(x):x in Generators(X)];

	XW:=sub<W|Gens>;
	
	"Verifying this embedding.";
	h:=hom<X->XW|x:->homembed(x)>;
	assert IsHomomorphism(h);
	assert #Kernel(h) eq 1;
	assert IsConjugate(XW,Stabiliser(X,1)@h,Stabiliser(XW,1));
	
	// Hence we will relabel XW to X.
	
	X:=XW;

	"Constructing As, the set of the subgroups A_i for i = 1, ..., 56.";

	As:=[Image(ph[i]):i in [1..#ph]];
	
	"Constructing C, the direct product of the subgroups A_i.";
	
	C:=sub<W|As>;
	
	"Constructing the intersection S of C and X, and the normaliser D of S in W.";

	S:=C meet X;
	D:=Normaliser(W,S);

	XStab:=Stabiliser(X,1);
	OrbsX:=OrbitRepresentatives(XStab);
	
	if graph then
		
		DStab:=Stabiliser(D,1);
		
		"Finding representative for the X-orbitals that are not D-orbitals.";
		
		NonSelfPaired:=[[1,o[2]]:o in OrbsX|o[1] ne #Orbit(DStab,o[2]) and not IsConjugate(X,[1,o[2]],[o[2],1])];
		SelfPaired:=[[1,o[2]]:o in OrbsX|o[1] ne #Orbit(DStab,o[2]) and IsConjugate(X,[1,o[2]],[o[2],1])];
		
		"Showing that among these X-orbitals, only one self-paired orbital Q is D-conjugate to a non-self-paired orbital.";
		
		ConjOrbitals:=[i:i in SelfPaired|exists{j:j in NonSelfPaired|IsConjugate(D,i,j)}];
		assert #ConjOrbitals eq 1;
		
		"Showing that the orbital graphs of the seven self-paired X-orbitals other than Q all have automorphism group equal to X.";
		
		num:=0;
		
		Grs:=[];
		
		for O in Exclude(SelfPaired,ConjOrbitals[1]) do
		
			num:=num+1;
		
			Gr:=Graph<Degree(X)|Set(O)^X>;
			
			// We use the Traces algorithms, allowing the automorphism group of any of our graphs to be calculated within a few minutes.
			Aut:=AutomorphismGroup(Gr:Al:="Traces");
			assert Aut eq X;
			
			"Verified automorphism group for graph", num, "of 7.";
			
			Append(~Grs,Gr);
			
		end for;
		
		"Veriyfying that the seven orbital graphs are all connected and pairwise non-isomorphic with valency 63.";
		
		assert forall{i:i in Grs|IsConnected(i)};
		assert forall{[i,j]:i in [1..#Grs],j in [1..#Grs]|i eq j or not IsIsomorphic(Grs[i],Grs[j])};
		assert forall{i:i in Grs|Valence(i) eq 63};
		
		"Verifying that, in each graph, no two vertices have the same closed neighbourhood.";
		// Since each graph is vertex-transitive, it suffices to show that the closed neighbourhood of a
		// fixed vertex is distinct from the closed neighbourhoods of all other vertices.
		
		for Gr in Grs do
			V:=Vertices(Gr);
			assert forall{i:i in [2..#V]|({V!1} join Neighbours(V!1)) ne ({V!i} join Neighbours(V!i))};
		end for;
		
	end if;

	if overgroups then
	
		"Constructing F_1.";
		
		A1:=As[1];
		F1:=A1;
		T1:=Stabiliser(X,Support(A1));
		for j in [2..#As] do
			Aj:=As[j];
			jr:=Rep(Support(Aj));
			T1j:=T1 meet Stabiliser(X,Support(Aj));
			A1j:=sub<C|A1,Aj>;
			U1j:=sub<W|A1j,T1j>; // The subgroup of W generated by A_{1j} and T_{1j}.
			GS:=GSet(U1j,{[1,jr]}); // The stabiliser in A_{1j} of each orbit of T_{1j} is equal to A_{1j} meet (the stabilisr in U_{1j}).
			mu,Q:=Action(U1j,GS);
			Orbs:=Orbits(T1j@mu);
			// F1j is the set of elements c_1 in F_1, such that there exists c_j in F_j where (1,...,1,c_1,1,...,1,c_j,1,...,1) stabilises each orbit of T_{1j} on Delta_i x Delta_j.
			F1j:=sub<A1j|(Stabiliser(Q,Orbs))@@mu meet A1j,Aj> meet A1;
			F1:=F1 meet F1j;
		end for;

		"Showing that F_1 lies in D.";

		assert F1 subset D;

		"Constructing all proper transitive subgroups of D containing S with order divisible by |X|.";
		
		function GenerateMaxes(MM)
		
			Maxes:=[];

			for m in MM do
				MMM:=MaximalSubgroups(m`subgroup:IsTransitive:=true);
				for n in MMM do
					if S subset n`subgroup and IsDivisibleBy(n`order,#X) then
						Append(~Maxes,n);
					end if;
				end for;
			end for;
			
			return Maxes;
			
		end function;

		M1:=MaximalSubgroups(D:IsTransitive:=true);
		"Subgroup construction step 1/7 complete.";
		M2:=GenerateMaxes(M1);
		"Subgroup construction step 2/7 complete.";
		M3:=GenerateMaxes(M2);
		"Subgroup construction step 3/7 complete.";
		M4:=GenerateMaxes(M3);
		"Subgroup construction step 4/7 complete.";
		M5:=GenerateMaxes(M4);
		"Subgroup construction step 5/7 complete.";
		M6:=GenerateMaxes(M5);
		"Subgroup construction step 6/7 complete.";
		M7:=GenerateMaxes(M6);
		"Subgroup construction step 7/7 complete.";

		"Showing that all subgroups constructed in step 7 have the same order as X.";

		assert forall{m:m in M7|m`order eq #X};
		
		// Hence, apart from X and D, any overgroup of X in D is conjugate to a subgroup in Subs, consisting of all
		// subgroups in M1 through M6.

		Subs:=&cat[M1,M2,M3,M4,M5,M6];

		"Performing final calculation on orbits of point stabilisers.";
		// We show that for each subgroup M in Subs, the number of orbits of a point stabiliser in M is less than the
		// number of orbits of a point stabiliser in X. (Hence this also holds when replacing M by D.)

		assert forall{M:M in Subs|#OrbitRepresentatives(Stabiliser(M`subgroup,1)) lt #OrbsX};
		
	end if;

end procedure;
