# Shoup: deterministic construction of irreducible polynomials over GF(2)

For every odd prime $q$ an irreducible polynomial of degree $q$ over $\mathbb{F}_2$ can be constructed deterministically in time polynomial in $q$. (Shoup's general method constructs irreducible polynomials of any degree $d$ over $\mathbb{F}_p$ deterministically in time polynomial in $d$ and $p$.)

## Proof sketch

Build the field $\mathbb{F}_{2^{q}}$ inside an extension obtained from roots of unity of order $q$, using Berlekamp factoring over small fields to find irreducible factors of cyclotomic polynomials, and then take the minimal polynomial of a suitable trace-compatible element, which has degree exactly $q$ since $q$ is prime.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Deterministic Berlekamp factorization over GF(2)](berlekamp-factorization-gf2.md)

## Sources

- Victor Shoup, "New Algorithms for Finding Irreducible Polynomials over Finite Fields", Mathematics of Computation 54(189), 1990.
