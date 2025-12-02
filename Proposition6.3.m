// Script to compute Igusa invariats for Proposition 6.3

K<z> := QuadraticField(5);
OK := Integers(K);
I2 := Factorization(2*OK)[1,1];

F<t> := FieldOfFractions(PolynomialRing(K,2));
R<x> := PolynomialRing(F);

C := HyperellipticCurve(5*x^6 - 12*x^5 + 10*t*x^3 + t^2);

L := IgusaInvariants(C);


// L[i] = J_{2i}

printf "Igusa Igusa Invariants:";

print(L);

// We will apply Theorem 1 of [Liu93]

// Case (I)

printf "The values of Case (I):";
print " ";

Case1 := [];
for i in [1..5] do
	Case1 := Append(Case1,L[i]^5/L[5]^i);
	print(L[i]^5/L[5]^i);
end for;

CaseI :=

[
	-5^5*t^2/3/(t-1)^2,
	-5^10*t^4/3^7/(t-1)^4, 
	5^5*t*(17*t+108)^5/3^18/(t-1)^6,
	-5^10*t^3*(23*t+27)^5/3^19/(t-1)^8
];


for i in [1..4] do
	assert Case1[i] eq CaseI[i];
end for;


// Definitions:

I2 := L[1]/12;
I4 := L[1]^2 - 24*L[2];
I6 := L[3];
I12 := -2^3*L[2]^3 + 3^2*L[1]*L[2]*L[3] - 3^3*L[3]^2 - L[1]^2*L[4];

I := [I2,I4,I6,0,0,I12]; // Now I[i] = I_{2i}



// Case (V)

eps := 3;
Case53 := 
[
	I4^eps/I[eps]^2,
	L[5]^eps/I[eps]^5,
	I12^eps/I[eps]^6,
	I4^(3*eps)/L[5]^eps/I[eps],
	I12^eps/L[5]^eps/I[eps],
];



for q in [3,5] do
	if q eq 3 then
		eps := 3;
	else
		eps := 1;
	end if;

	printf "The values of Case (V) for q = %o :",q;
 	print " ";

	I4^eps/I[eps]^2;
	L[5]^eps/I[eps]^5;
	I12^eps/I[eps]^6;
	I4^(3*eps)/L[5]^eps/I[eps];
	I12^eps/L[5]^eps/I[eps];
end for;

d := (17*t + 108);
CaseV3 := 

[
	3^12*5^4*t^2/d^2,
	3^18*(t-1)^6/5^5/t/d^5,
	3^27*(t-1)^3*(9*t+16)^3/d^6,
	3^18*5^17*t^7/d/(t-1)^6,
	3^9*5^5*t*(9*t+16)^3/d/(t-1)^3

];

for i in [1..5] do
	 Case53[i] eq CaseV3[i];
end for;



