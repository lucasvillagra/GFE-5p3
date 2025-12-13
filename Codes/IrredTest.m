// Script to check the conductor exponent at (sqrt(5)) in Theorem 7.8

/* We want to check irreducibility of F(x) over Q_5,
		where F(x) = a^5f(x/a) + 2a^5 + 4c^3 
							 = x^5 - 5a^2x^3 + 5a^4*x + 2a^5 + 4c^3

	By Lemma 3.11, it only depend on a,c mod 25.
*/

_<x> := PolynomialRing(pAdicField(5, 30));


for a in [0..24] do
	for c in [0..24] do

		F := x^5 - 5*a^2*x^3 + 5*a^4*x + 2*a^5 + 4*c^3;

		if not IsDivisibleBy(c*(a^5+c^3),5) then // 5 nmid ab
				
			if IsDivisibleBy(a,5) then // 5 mid a
				a0 := Integers()!(a/5^Valuation(a,5));
				list := [6, 8, 17, 19];

				for n in [0..24] do
					if c^3 mod 25 eq n*a^5 mod 25 then
						if n in list then
							assert not IsIrreducible(F);
						else
							assert IsIrreducible(F);
						end if;
					end if;
				end for;

			else	// 5 nmid a

				list := [6, 12, 18];

				for n in [0..24] do
					if c^3 mod 25 eq n*a^5 mod 25 then
						if n in list then
							assert not IsIrreducible(F);
						else
							assert IsIrreducible(F);
						end if;
					end if;
				end for;
						
			end if;

		end if;
	end for;
end for;




