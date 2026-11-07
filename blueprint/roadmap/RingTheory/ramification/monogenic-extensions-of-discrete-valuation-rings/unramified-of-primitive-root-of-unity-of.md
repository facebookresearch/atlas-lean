# Adjoining a root of unity of order coprime to the residue characteristic is unramified

Let $A$ and $B$ be discrete valuation rings, with $A$ complete with respect to its maximal
ideal, and let $B$ be an $A$-algebra via a local homomorphism $A \to B$, such that $B$ is
finitely generated and torsion-free as an $A$-module. Let $k_A$ and $k_B$ be the residue fields
of $A$ and $B$. Let $n$ be a natural number coprime to the characteristic of $k_A$, and let
$\zeta \in B$ be a primitive $n$-th root of unity with $B = A[\zeta]$. Then $k_B$ is separable
over $k_A$ and the rank of $B$ as an $A$-module equals $[k_B : k_A]$.

Coprimality is meant literally, with $\gcd(n, 0) = n$, so when $k_A$ has characteristic $0$
the hypothesis forces $n = 1$.

## Sources

- ATLAS NumberTheoryI, the helper `cor_10_16_of_adjoin` for Corollary 10.16; the generation $B = A[\zeta]$ is assumed here rather than proved from the integral-closure setup.
