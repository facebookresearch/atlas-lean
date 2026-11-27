# Schumacher compression

Let $\rho$ be a density operator on $\mathbb{C}^\Sigma$, $\alpha > 0$ and $\delta \in (0,1)$. If $\alpha > S(\rho)$,
then for all but finitely many $n$ there is a quantum coding scheme that encodes $\rho^{\otimes n}$ into
$\lfloor \alpha n \rfloor$ qubits with entanglement fidelity at least $1 - \delta$: for a
[purification](../quantum-foundations/purification-and-unitary-equivalence-of-purifications.md) $|\psi\rangle$ of
$\rho^{\otimes n}$ on the system and a reference, encoding channel $\mathcal{E}_n$ and decoding channel $\mathcal{D}_n$,
$\langle \psi | \big( (\mathcal{D}_n \circ \mathcal{E}_n) \otimes \mathrm{id} \big)(|\psi\rangle\langle\psi|) | \psi \rangle \ge 1 - \delta$,
the square of the root fidelity of the two states (Watrous (5.220) uses the root fidelity itself; the theorem is the
same, since it quantifies over every tolerance $\delta$) (comparing input and output states of the system alone would not do:
a constant channel can destroy the entanglement with the reference). If $\alpha < S(\rho)$, such
a scheme exists for only finitely many $n$.

## Depends on

- [Quantum channel](../quantum-operations/quantum-channel.md)
- [Von Neumann entropy and Holevo information](classical-quantum-information/von-neumann-entropy-and-holevo-information.md)
- [Fidelity of positive semidefinite matrices](../quantum-states-distances-and-entropy/density-matrices-and-fidelity/root-fidelity.md)
- [Purification and unitary equivalence of purifications](../quantum-foundations/purification-and-unitary-equivalence-of-purifications.md)

## Proof depends on

- [AEP and typical sets (finite iid)](../../InformationTheory/source-coding/remaining-clauses-of-aep-and-typical-sets.md)
- [Typical subspace](typical-subspace.md)
- [Small-projector converse lemma](small-projector-converse-lemma.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Theorem 5.44. <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
