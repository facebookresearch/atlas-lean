# Resolution is not simulated by unary Sherali–Adams: low-degree simulations need exponentially large coefficients

There are $n$-variate CNF formulas $F_n$ refutable by constant-width Resolution such that every Sherali–Adams refutation of $F_n$ of degree $n^{o(1)}$ uses coefficients of magnitude $\exp(n^{\Omega(1)})$. This is tight up to the exponent: a degree-$d$ SA refutation can always be chosen with integer coefficients of magnitude $\exp(n^{O(d)})$. With lifting, every SA refutation must use exponentially many monomials or exponentially large coefficients, so Resolution is not $p$-simulated by unary Sherali–Adams, although Sherali–Adams with arbitrary coefficients simulates width-$w$ Resolution in degree $w+1$ and, when twin variables are allowed, $p$-simulates Resolution.

## Proof sketch

Take $F_n$ to encode the SINK-OF-DAG principle, which is stronger than SINK-OF-POTENTIAL-LINE and has constant-width Resolution refutations. In a low-degree SA refutation $\sum_ip_i\overline{C_i}=1+J$, the absence of low-degree $\tfrac12$-NS refutations of SoPL forces $1+J(x)\ge1.5$ for some input $x$. Iterating the argument by combining $i$ SoPL instances inside SINK-OF-DAG produces inputs $x_i$ with $1+J(x_i)\ge1.5^{\Omega(i)}$; taking $i=\mathrm{poly}(n)$ and noting that the right-hand side is bounded by the total coefficient magnitude times the number of monomials gives the bound.

## Depends on

- [Unary Nullstellensatz and unary Sherali–Adams refutations of CNF formulas](unary-nullstellensatz-and-unary-sherali-adams.md)
- [Resolution refutation](../../../../Logic/propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../../../Logic/propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

- [Approximate Nullstellensatz lower bound for the sink-of-potential-line formulas via approximate degree of OR](approximate-nullstellensatz-sink-of-potential-line.md)
- [PLS^dt is characterized by Resolution: PLS^dt(S(F)) = Θ(Res(F))](pls-dt-characterized-by-resolution.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
