# Polynomial-time real-root isolation by Sturm sequences

Given a nonzero univariate polynomial with rational coefficients (in binary), its Sturm sequence and a list of disjoint rational intervals, each containing exactly one real root and together containing all real roots, are computable in time polynomial in the coefficient bit length; the number of sign variations of the Sturm sequence at a rational point is computable in time polynomial in the coefficient bit length plus the bit length of the point.

## Proof sketch

Sturm's theorem counts distinct real roots in an interval by the difference of sign variations; root separation bounds (Mahler) show that bisection to polynomially many bits isolates all roots, and the subresultant bounds keep the Sturm sequence's coefficients polynomially sized.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Polynomial-time rational Gaussian elimination (Bareiss)](bareiss-rational-gaussian-elimination.md)
- [Mahler–Mignotte root separation bound](../../algebraic-complexity/real-root-counting-and-separation/mahler-mignotte-root-separation.md)
- [Sturm's theorem for arbitrary nonzero real polynomials via reduced Sturm sequences](../../algebraic-complexity/real-root-counting-and-separation/sturm-theorem-via-reduced-sturm-sequences.md)

## Sources

- Lee E. Heindel, "Integer Arithmetic Algorithms for Polynomial Real Zero Determination", Journal of the ACM 18(4), 533–548, 1971.
- Saugata Basu, Richard Pollack and Marie-Françoise Roy, "Algorithms in Real Algebraic Geometry", 2nd ed., Springer, 2006.
- Kurt Mahler, "An Inequality for the Discriminant of a Polynomial", Michigan Mathematical Journal 11(3), 257–262, 1964.
