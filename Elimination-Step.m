// Series of functions used to eliminate Newforms using Mazur's method

_<x> := PolynomialRing(Rationals());
K := NumberField(x^2-5);
OK := Integers(K);


// CASE 1: Function to eliminate a newform at t \neq 0, infinity using one prime
/*
	INPUT:
		- form : Eigenform of a Hilbet newform
		- l : A prime 
		- candidates : A list of the possible Hecke polynomials
		

	OUTPUT:
		The function returns a bound C such that the newform "form" can 
		be discarded for p > C.
*/

NewformBound := function(form,l,candidates)
	local Idl, Eig, poly;

	Idl := Factorisation(l*OK)[1][1];
	Eig := HeckeEigenvalue(form,Idl);
	poly := MinimalPolynomial(Eig);

	return LeastCommonMultiple([Numerator(Resultant(poly,pp)) : pp in candidates]);
end function;

// CASE 2: corresponding to the elimination procedure when t=0 or t=oo
// The difference is that the representation is looked over F.
/*
	INPUT:
		- form : Hilbet newform
		- l : A prime 
		- candidates : A list of polynomials
		
	OUTPUT:
		The function returns the a bound C such that the newform "form" can 
		be discarded for  p > C, only considering the value t=0
*/

NewformBoundOverF:=function(form,l,candidates)
	local Idl, Eig, poly, F, OF, f1, f2;

	Idl := Factorisation(l*OK)[1][1];
	Eig := HeckeEigenvalue(form,Idl);
	F := NumberField(CyclotomicPolynomial(15));
	OF := Integers(F);
	f1 := InertiaDegree(Factorisation(l*OF)[1][1]);
	f2 := InertiaDegree(Factorisation(l*OK)[1][1]);

	if f1/f2 eq 2 then
	   Eig := Eig^2-2*l^f2;
	end if;
	poly := MinimalPolynomial(Eig);

	return LeastCommonMultiple([Numerator(Resultant(poly,pp)) : pp in candidates] cat [l]);
end function;

//=====================================================================================
// CASE 3: when q | t-1.
/*
	INPUT:
		- form : A Hilbert newform
		- P : A list of primes. The default value is the set [7,11,17,19,29,31].

	OUTPUT:
		The function returns the a bound C such that the newform "form" can 
		be discarded for p > C, for Case 3 (i.e. q | t-1 for all q in P)
*/


Eliminate_FormLL := function(form,l)
 	local Bd, I;

	I :=Factorisation(l*OK)[1][1];
	Bd := [];
	Bd:= Bd cat [Numerator(Norm(HeckeEigenvalue(form,I) - Norm(I) - 1)),Numerator(Norm(HeckeEigenvalue(form,I) + Norm(I) + 1))];
	Bd := LeastCommonMultiple(Bd);

	return Bd;
end function;


//=====================================================================================
// Use the previous code to discard a newform in either case 1, 2, 3 for a prime l.
/*
	INPUT:
		- form : A Hilbert newform
		- l : A prime.
		- Cd1 : A list of the possible Hecke polynomials in Case 1
		- Cd2 : A list of possible polynomials at 0.
		- Cd3 : A list of possible polynomials at oo.
	OUTPUT:
		The function returns the a bound C such that the newform "form" can 
		be discarded for p > C, for Case 3 (i.e. q | t-1 for all q in P)
*/


MazurBound :=  function(form,l,C1,C0,Coo)

	local Bd1, Bd2, Bd3, Bd4, Bd;

	Bd1 := NewformBound(form,l,C1);
	Bd2 := NewformBoundOverF(form,l,C0);
	Bd3 := NewformBoundOverF(form,l,Coo);
	Bd4 := Eliminate_FormLL(form,l);
	Bd := LeastCommonMultiple([Bd1] cat [Bd2] cat [Bd3] cat [Bd4]);

	return Bd;
end function;

//=====================================================================================
// Same as before but for many primes together.
/*
	INPUT:
		- form : A Hilbert newform
		- P : A set of primes.
		- Cd1 : A list of the possible Hecke polynomials in Case 1 for all primes in P.
		- Cd2 : A list of possible polynomials at 0 for all primes in P.
		- Cd3 : A list of possible polynomials at oo for all primes in P.
	OUTPUT:
		The function returns the a bound C such that the newform "form" can 
		be discarded for p > C, for Case 3 (i.e. q | t-1 for all q in P)
*/


TheoremABound := function(form, list)

  	local Bd, ans;
	
	Bd := [];

	for i in [1..#list] do
		Bd := Append(Bd,MazurBound(form ,list[i][1], list[i][2], list[i][3], list[i][4]));
	end for;

	Bd := GreatestCommonDivisor(Bd);

	if Bd ne 0 then
		ans := PrimeFactors(Bd);
		if #ans eq 0 then
			ans := [2];
		end if;
	else
		ans := [];
	end if;

	return ans;

end function;


//=====================================================================================
// Main routine to prove Theorem A.
	/*
		INPUT:
			- i : Power of the prime 3
			- j : Power of the prime (sqrt(5))
			- P : A list of primes. The default value is the set [7,11,17,19,29,31].
			- Cd : A list of polynomials. The default will be the candidates obtained
						   for each prime p in P.

		OUTPUT:
			The function prints for each newform in the space of level 3^i*(sqrt(5))^j 
			whether or not it can be discarded using primes in P 
			It also returns the list for which the newforms can be discarded if p is not in the list.
	*/


TheoremA := function(i,j,list : flag := false)
	
	local I5, M, decomp, Good, Bad, P;
	
	I5 := Factorisation(5*OK)[1][1];
	M := HilbertCuspForms(K,3^i*I5^j);
	decomp := NewformDecomposition(NewSubspace(M));
	Bd := {};
	Good := [];
	Bad := [];

	P := [];
	for i in [1..#list] do
		P := Append(P,list[i][1]);
	end for;

	for i in [1..#decomp] do
	    f := Eigenform(decomp[i]);
		ans := TheoremABound(f,list);
		if #ans ne 0 then
			Bd := Bd join Set(ans);
			Good := Append(Good,i);
			if flag then
				printf "i = %o of %o, small exponents after elimination = %o\n",i,#decomp,ans;
			end if;
		else
			Bad := Append(Bad,i);
			if flag then
				printf "i = %o of %o failed using %o\n",i,#decomp,P;
			end if;
		end if; 
	end for;

	printf "The newforms %o cannot be discarded using primes in %o.",Bad,P;
	print "  ";
	printf "The newforms %o can be discarded for p outside",Good;  
	return " ", Sort(SetToSequence(Bd));
end function;



