# The number of stabilizer states

The number of $n$-qubit [stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md),
counted as states up to global phase, is

$$N_n = 2^n \prod_{k=0}^{n-1} \big( 2^{n-k} + 1 \big) = 2^{(1/2 + o(1)) n^2} .$$

Proof: $N_n = G / A$, where $G$ counts ordered generating sets $M_1, \dots, M_n$ of stabilizer groups and $A$ counts the
generating sets of one group. Ignoring signs, $M_1$ has $4^n - 1$ choices, and $M_k$ must commute with
$M_1, \dots, M_{k-1}$ without lying in the group they generate, which leaves $4^n / 2^{k-1} - 2^{k-1}$ choices; each
generator then takes one of two signs. A fixed group of order $2^n$ has $\prod_{k=0}^{n-1} (2^n - 2^k)$ ordered
generating sets. For example $N_1 = 6$, the states $|0\rangle, |1\rangle, |\pm\rangle$ and $(|0\rangle \pm i|1\rangle)/\sqrt 2$.

## Depends on

- [Stabilizer groups and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](pauli-operators-commute-iff-symplectic-product-vanishes.md)

## Sources

- S. Aaronson and D. Gottesman, *Improved simulation of stabilizer circuits*, Phys. Rev. A 70 (2004), 052328, arXiv:quant-ph/0406196, Section II, Proposition 2 and its proof.
