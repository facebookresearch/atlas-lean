# Output distributions of shallow circuits do not concentrate on two distant sets

Let $\rho$ be an $n$-qubit state of circuit depth $d$ and let $p$ be the distribution of the outcome of measuring all $n$ qubits in the computational basis. For all $S_1, S_2 \subseteq \{0,1\}^n$ at Hamming distance at least $D$,

$$
p(S_1)\, p(S_2) \le 4 \exp\!\left( - \frac{D^2}{2^{O(d)}\, n} \right).
$$

The same holds for measurement in any product basis, in particular the Hadamard ($X$) basis.

## Proof sketch

Each output qubit depends on at most $2^d$ input qubits through the light cone of the circuit, and each input qubit influences at most $2^d$ outputs. Measuring the input-side ancillas first, the output distribution becomes a function of independent sources with bounded influence, and a martingale (McDiarmid-type) concentration inequality shows that the Hamming distance to any set of measure at least $p(S_1)$ concentrates, so a set at distance $D$ has small measure.

## Depends on

- [Circuit depth of a quantum state and trivial states](trivial-states-of-bounded-circuit-depth.md)

## Proof depends on

- [Circuit depth of a quantum state and trivial states](trivial-states-of-bounded-circuit-depth.md)

## Sources

- Anurag Anshu, Chinmay Nirkhe, "Circuit lower bounds for low-energy states of quantum code Hamiltonians", ITCS (2022); arXiv:2011.02044.
- Lior Eldar, Aram W. Harrow, "Local Hamiltonians whose ground states are hard to approximate", FOCS (2017); arXiv:1510.02082.
- Anurag Anshu, Nikolas P. Breuckmann, Chinmay Nirkhe, "NLTS Hamiltonians from good quantum codes", STOC (2023); arXiv:2206.13228.
