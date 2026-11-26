# The Clifford group modulo Pauli operators is the symplectic group

Let $\mathcal{C}_n$ be the $n$-qubit Clifford group (unitaries $U$ with $U \mathcal{P}_n U^{*} = \mathcal{P}_n$). For
$U \in \mathcal{C}_n$ there is a unique $\mathbb{F}_2$-linear map $\sigma_U : \mathbb{F}_2^{2n} \to \mathbb{F}_2^{2n}$ with
$U X^a Z^b U^{*} \in \{\pm 1, \pm i\} \cdot X^{a'} Z^{b'}$ where $(a', b') = \sigma_U(a, b)$. The map $\sigma_U$ preserves
the [symplectic product](../stabilizer-formalism/symplectic-product-of-pauli-operators.md), $U \mapsto \sigma_U$ is a
surjective homomorphism $\mathcal{C}_n \to \mathrm{Sp}(2n, \mathbb{F}_2)$, and its kernel is the Pauli group with arbitrary
phases, $\{ e^{i\theta} P : P \in \mathcal{P}_n \}$. Hence

$$\mathcal{C}_n / \big(U(1) \cdot \mathcal{P}_n\big) \;\cong\; \mathrm{Sp}(2n, \mathbb{F}_2).$$

Up to signs, a Clifford circuit acts on Pauli operators as a binary symplectic matrix. A classical simulation must
track the signs as well: $I$ and $X$ induce the same binary matrix but give opposite deterministic outcomes when $Z$ is
measured on $|0\rangle$.

## Depends on

- [The Clifford group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/clifford-group-on-n-qubits.md)
- [Symplectic product of Pauli operators](../stabilizer-formalism/symplectic-product-of-pauli-operators.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](../stabilizer-formalism/pauli-operators-commute-iff-symplectic-product-vanishes.md)
- [A unitary is determined up to phase by its conjugation action on Pauli operators](unitary-determined-up-to-phase-by-conjugation-of-paulis.md)
- [Canonical form of Clifford circuits](canonical-form-of-clifford-circuits.md)

## Informally uses

- [Conjugation of Pauli operators by $H$, $S$ and CNOT](conjugation-of-pauli-operators-by-h-s-and-cnot.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 3.5 ("$C_n/P_n' \cong Sp(2n, Z_2)$").
- A. R. Calderbank, E. M. Rains, P. W. Shor and N. J. A. Sloane, *Quantum error correction via codes over GF(4)*, IEEE Trans. Inform. Theory 44 (1998), 1369–1387, arXiv:quant-ph/9608006, Section 2 (the properties of the Clifford group $L$: $L / \langle E, \eta I \rangle$ is isomorphic to $\mathrm{Sp}_{2n}(2)$).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 5.3.
