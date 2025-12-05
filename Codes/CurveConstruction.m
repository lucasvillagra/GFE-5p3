// Script to find the hyperelliptic curve C^+_{5,3} (see Section 7.1)


FF<t> := FunctionField(Rationals());
A<x,y,z> := ProjectiveSpace(FF,2);
C := Curve(A,y^15*z^2-x^2*(z-x)^7*(z-t*x)^8/t^3);
phiAmb := map<A->A|[y*z/t,(x-z)*(z-t*x)/t,x*y]>;
phi := Restriction(phiAmb,C,C);  

phiAmb4 := map<A->A|[(x-z)/(t*x-z),(t-1)*(z-x)^2*(t*x-z)*x/t/y^4,1]>;
phi4 := Restriction(phiAmb4,C,C);  

Mp := iso<C->C|DefiningEquations(phi),DefiningEquations(phi)>;
Mp4 := iso<C->C|DefiningEquations(phi4),DefiningEquations(phi4)>;
G := AutomorphismGroup(C,[Mp4,Mp]);
time D,map := CurveQuotient(G);
D;
