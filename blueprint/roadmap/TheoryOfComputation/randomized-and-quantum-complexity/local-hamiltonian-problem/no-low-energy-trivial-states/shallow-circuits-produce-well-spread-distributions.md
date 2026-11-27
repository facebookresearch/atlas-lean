# Output distributions of shallow circuits do not concentrate on two distant sets

Let $\rho$ be an $n$-qubit state of circuit depth $d$ and let $p$ be the distribution of the outcome of measuring all $n$ qubits in the computational basis. For all $S_1, S_2 \subseteq \{0,1\}^n$ at Hamming distance at least $D$,

$$
p(S_1)\, p(S_2) \le 4 \exp\!\left( - \frac{D^2}{2^{O(d)}\, n} \right).
$$

The same holds for measurement in any product basis, in particular the Hadamard ($X$) basis.

## Proof sketch

Write the purified state as $U|0\rangle^{\otimes m}$ with $U$ of depth $d$; by light cones one may take $m \le 2^d n$. The commuting Hamiltonian $G = \frac1m\sum_{i=1}^{m} U |1\rangle\langle 1|_i U^\dagger$ has locality $2^d$, unique ground state $U|0\rangle^{\otimes m}$ and eigenvalues in $\{0, 1/m, \dots, 1\}$. A Chebyshev-type polynomial $P$ of degree $f$ with $P(0) = 1$ and $|P(j/m)| \le \exp(-f^2/(100 m))$ for $j \ge 1$ makes $P(G)$ an approximate projector onto the ground state, and $P(G)$ acts on at most $f \cdot 2^d$ qubits at a time, so with $\Pi_{S}$ the projection onto strings in $S$ (tensored with the identity on ancillas), $\Pi_{S_1} P(G) \Pi_{S_2} = 0$ once $f 2^d < D$. Since $\| |\rho\rangle\langle\rho| - P(G) \| \le \exp(-f^2/(100m))$ for $|\rho\rangle = U|0\rangle^{\otimes m}$, it follows that $\sqrt{p(S_1)\,p(S_2)} = \|\Pi_{S_1}|\rho\rangle\langle\rho|\Pi_{S_2}\| \le \exp(-f^2/(100m))$; taking $f$ just below $D/2^d$ gives the bound.

## Depends on

- [Circuit depth of a quantum state and trivial states](trivial-states-of-bounded-circuit-depth.md)

## Sources

- Anurag Anshu, Chinmay Nirkhe, "Circuit lower bounds for low-energy states of quantum code Hamiltonians", ITCS (2022); arXiv:2011.02044.
- Lior Eldar, Aram W. Harrow, "Local Hamiltonians whose ground states are hard to approximate", FOCS (2017); arXiv:1510.02082.
- Anurag Anshu, Nikolas P. Breuckmann, Chinmay Nirkhe, "NLTS Hamiltonians from good quantum codes", STOC (2023); arXiv:2206.13228.
