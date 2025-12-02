//=====================================================================================
// Script to compute the data of Table 6.1
/*
      INPUT:
         - i : the exponent of 3.
	     - j : the exponent of \sqrt{5}
*/	     

Table := function(i,j)

	local K, OK, I5, M, decomp, Field;

	_<x> := PolynomialRing(Rationals());
	K := NumberField(x^2-5);
	OK := Integers(K);
	I5 := Factorisation(5*OK)[1][1];
	M := HilbertCuspForms(K, 3^i*I5^j);
	decomp := NewformDecomposition(NewSubspace(M));
	Field := [k : k in [1..#decomp] | IsIsomorphic(K,CoefficientField(Eigenform(decomp[k])))];

	return [Dimension(M),#decomp,#Field];

end function;