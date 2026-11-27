# Hastings-Haah-O'Donnell: fiber bundle codes break the polylog square-root barrier

There is a family of quantum LDPC codes, the *fiber bundle codes*, with distance $d = \Omega(n^{3/5}/\mathrm{polylog}(n))$ and dimension $k = \tilde\Theta(n^{3/5})$. They are obtained by twisting the homological product of a random classical LDPC code (base) with a cycle (fibre) by a random collection of circle automorphisms.

## Proof sketch

In a fiber bundle the fibre homology over each base cycle is twisted by the holonomy given by the random automorphisms. Logical cycles must wind around twisted fibres coherently; an expansion argument for the random twisting shows that any $Z$-logical has weight at least $n^{3/5}$ up to logs, while $X$-logicals are controlled by the base code's distance. Distance balancing equalizes the two.

## Depends on

- [Quantum LDPC code families and asymptotically good quantum codes](quantum-ldpc-code-families-and-good-codes.md)

## Proof depends on

- [Parameters of hypergraph product codes](parameters-of-hypergraph-product-codes.md)
- [Balanced products of chain complexes over a group](balanced-product-of-chain-complexes.md)

## Sources

- Matthew B. Hastings, Jeongwan Haah, Ryan O'Donnell, "Fiber bundle codes: breaking the N^{1/2} polylog(N) barrier for quantum LDPC codes", STOC (2021); arXiv:2009.03921.
