# Polynomial-time real-root isolation by Sturm sequences

Given a univariate polynomial with rational coefficients (in binary), its Sturm sequence, the number of sign variations at rational points, and a list of disjoint rational intervals each containing exactly one real root and together containing all real roots, are computable in time polynomial in the coefficient bit length.

## Proof sketch

Sturm's theorem counts distinct real roots in an interval by the difference of sign variations; root separation bounds (Mahler) show that bisection to polynomially many bits isolates all roots, and the subresultant bounds keep the Sturm sequence's coefficients polynomially sized.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Polynomial-time rational Gaussian elimination (Bareiss)](bareiss-rational-gaussian-elimination.md)

## Sources

- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
