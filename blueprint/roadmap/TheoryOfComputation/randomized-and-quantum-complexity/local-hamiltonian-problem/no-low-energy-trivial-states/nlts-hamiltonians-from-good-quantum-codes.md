# NLTS theorem (Anshu-Breuckmann-Nirkhe)

There is a family of commuting frustration-free $(k, \ell)$-local Hamiltonians $H^{(n)}$ with $k, \ell = O(1)$, namely the code Hamiltonians of asymptotically good quantum Tanner codes, and a constant $\varepsilon > 0$ such that every $n$-qubit state of relative energy $\varepsilon$ has circuit depth $\Omega(\log n)$. In particular the NLTS conjecture holds.

## Proof sketch

Take a low-energy state $\rho$ and measure it in the $Z$ basis: by Markov's inequality most mass sits on strings with small $Z$-syndrome, which by clustering fall into classes at pairwise Hamming distance $\Omega(n)$. If $\rho$ had depth $o(\log n)$, the spread lemma with $D = \Omega(n)$ forces almost all of this mass into a single cluster; the same holds in the $X$ basis. But then both logical labels are nearly deterministic, contradicting the uncertainty relation since the code has $k = \Theta(n)$ logical qubits. The argument needs constant rate, linear distance and the expansion property simultaneously, supplied by good quantum LDPC codes.

## Depends on

- [The NLTS property and the Freedman-Hastings conjecture](no-low-energy-trivial-states-property.md)
- [CSS code Hamiltonians of quantum LDPC codes](css-code-hamiltonians.md)
- [Bounded-degree local Hamiltonian families and relative energy](normalized-local-hamiltonian-families-and-relative-energy.md)
- [Circuit depth of a quantum state and trivial states](trivial-states-of-bounded-circuit-depth.md)

## Proof depends on

- [Output distributions of shallow circuits do not concentrate on two distant sets](shallow-circuits-produce-well-spread-distributions.md)
- [Clustering of low-syndrome strings for codes with small-set boundary expansion](clustering-of-low-syndrome-strings.md)
- [Uncertainty relation for complementary logical measurements](uncertainty-relation-for-logical-cluster-labels.md)
- [Leverrier-Zemor: quantum Tanner codes are asymptotically good](../../../../QuantumInformation/quantum-error-correction/asymptotically-good-quantum-ldpc-codes/quantum-tanner-codes-have-linear-distance.md)

## Sources

- Anurag Anshu, Nikolas P. Breuckmann, Chinmay Nirkhe, "NLTS Hamiltonians from good quantum codes", STOC (2023); arXiv:2206.13228.
