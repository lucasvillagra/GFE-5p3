// Bounds in Corollary 6.6

/* Function to compute the Bound to prove irreducibility 
under the condition  l\nmid b for l=3,5.
*/

/*
	INPUT:
		- N : the norm of a prime having potentially good reduction
		- f : the inertial degree of F/K
		- c : the inertial exponent of A

	OUTPUT:
		The function returns the a bound C for p such that if p>C,
		the representation is irreducible at p

*/

BoundIrreducibility := function(N,f,c)

	local  R, M, s, p, i, O;

	_<y> := PolynomialRing(Integers());
	K<z> := NumberField(y^2-5);
	O:=Integers(K);
	_<x> := PolynomialRing(O);
	R := 1;

	for a in [-4*Floor(N^(1/2))..4*Floor(N^(1/2))] do
		M := Floor(((16*N-a^2)/5)^(1/2));
		for b in [-M..M] do
			if a mod 2 eq b mod 2 then
			        s := O!((a+b*z)/2);
				R := R * Resultant(x^c-1,x^2-s*x+N^f);
			end if;
		end for;
	end for;

	p , i := Max(PrimeDivisors(Integers()!Norm(R)));

	return p;
end function;