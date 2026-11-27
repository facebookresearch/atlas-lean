# An explicit polynomial-time affine disperser for dimension O(N^{4/5})

There is a family $f_N:\{0,1\}^{N}\to\{0,1\}$, computable in time polynomial in $N$, such that $f_N$ is an affine disperser for dimension $d(N)=O(N^{4/5})$. It is obtained by choosing an odd prime $q\in(M,2M]$ with $M\approx N^{3/5}$, constructing an irreducible polynomial of degree $q$ over $\mathbb{F}_2$ deterministically, identifying $\mathbb{F}_2^{N}$ with coordinates in $\mathbb{F}_{2^{q}}$, and evaluating a Ben-Sasson–Kopparty subspace-polynomial test.

## Proof sketch

The irreducible polynomial gives explicit arithmetic in $\mathbb{F}_{2^{q}}$; Ben-Sasson–Kopparty show that the chosen polynomial cannot be constant on any affine subspace of the given dimension, because its restriction would be a low-degree subspace polynomial with too many roots.

## Depends on

- [Affine dispersers](../gate-elimination-and-explicit-lower-bounds/affine-dispersers.md)

## Proof depends on

- [Shoup: deterministic construction of irreducible polynomials over GF(2)](../../../../polynomial-time-problems/exact-algebraic-and-combinatorial-algorithms/shoup-irreducible-polynomials.md)

## Sources

- Eli Ben-Sasson and Swastik Kopparty, "Affine Dispersers from Subspace Polynomials", SIAM Journal on Computing 41(4), 2012.
- Victor Shoup, "New Algorithms for Finding Irreducible Polynomials over Finite Fields", Mathematics of Computation 54(189), 1990.
