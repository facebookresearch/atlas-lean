# Deterministic Berlekamp factorization over GF(2)

Every polynomial $f\in\mathbb{F}_2[x]$ of degree $d$ can be factored into irreducibles by a deterministic algorithm in time polynomial in $d$. In particular irreducibility over $\mathbb{F}_2$ is decidable in polynomial time.

## Proof sketch

After removing repeated factors via $\gcd(f,f')$, the Berlekamp subalgebra $\{g : g^{2}\equiv g\pmod f\}$ is the kernel of $Q-I$ for the Frobenius matrix $Q$; its dimension is the number of irreducible factors, and for a nontrivial element $g$ the gcds $\gcd(f,g)$ and $\gcd(f,g+1)$ split $f$. Since the field has two elements, trying both constants is deterministic.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Polynomial-time rational Gaussian elimination (Bareiss)](bareiss-rational-gaussian-elimination.md)

## Sources

- Elwyn R. Berlekamp, "Factoring Polynomials over Finite Fields", Bell System Technical Journal 46, 1967.
