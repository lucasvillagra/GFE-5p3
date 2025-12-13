// Script to verify computations in Lemma 7.3

K := QuadraticField(5);
OK := Integers(K);
R<x> := PolynomialRing(K);

P := [7,11,29]; 

C_5 := HyperellipticCurve(x^6 + 6*x^5 - 45*x^4 - 270*x^3 + 405*x^2 + 2592*x + 972);
C_53 := HyperellipticCurve(5*x^6 - 12*x^5 + 30*x^3 + 9);

//==============================================
// Computing Table 7.1

print "The following is Table 7.1:";
for p in P do
	Id := Factorisation(p*OK)[1][1];
	print(<p,Reverse(R!EulerFactor(C_53,Id)),Reverse(R!EulerFactor(C_5,Id))>);
end for;
print " ";
//==============================================
// Proving congruence mod 3

for p in P do
	Id := Factorisation(p*OK)[1][1];
	f := Reverse(R!EulerFactor(C_53,Id));
	ftwist := Evaluate(f,Norm(Id)*x);
	coef1 := Coefficients(ftwist);
	coef2 := Coefficients(Reverse(R!EulerFactor(C_5,Id)));

	for i in [1..#coef1] do
		assert Integers()!coef1[i] mod 3 eq Integers()!coef2[i] mod 3;
	end for;
end for;

//==============================================
/* Characteristic polynomial of the Frobenius 
   endomorphism acting on E_3(3)*/

print "Characteristic polynomial of the Frobenius 
   endomorphism acting on E_3(3)";

E3 := EllipticCurve([3,0,3,0,0]);
E3 := BaseExtend(E3,K);
for p in P do
	Id := Factorisation(p*OK)[1][1];
	print(<p,x^2 - TraceOfFrobenius(E3,Id)*x + Norm(Id)>);
end for;

//==============================================
// Proving congruence mod sqrt(5)

for p in P do
	Id := Factorisation(p*OK)[1][1];
	f1 := x^2 - TraceOfFrobenius(E3,Id)*x + Norm(Id); 
	f1 := f1^2;
	coef1 := Coefficients(f1);

	f2 := R!EulerFactor(C_53,Id);
	f2twist := Evaluate(f2,Norm(Id)*x);
	coef2 := Coefficients(Reverse(f2twist));

	for i in [1..#coef1] do
		assert Integers()!coef1[i] mod 5 eq Integers()!coef2[i] mod 5;
	end for;
end for;






