# Unitarity, norm preservation and probabilities in encoded circuit semantics

Gate application for arbitrary encoded entries is a separate definition, listed under the dependencies; it does not
assert unitarity. This node collects the laws that need well-formedness hypotheses.

## Expansion

A sound expansion has separate pages for:

1. **Unitarity.** For a well-formed gate (its $4 \times 4$ entry matrix unitary, acting on qubits $i < j < N$),
   gate application is the action of a unitary on $\mathbb{C}^{2^N}$, obtained by conjugating the entry matrix tensored with
   the identity by the qubit permutation that brings $i$ and $j$ first.
2. **Norm preservation.** Applying a list of well-formed gates preserves the squared norm; the initial state is a unit
   vector.
3. **Probabilities.** For unit vectors, the acceptance probability lies in $[0,1]$ and acceptance and rejection
   probabilities sum to $1$.
4. **Composition.** Applying the concatenation of two gate lists equals applying the second after the first.

## Depends on

- [Applying a 2-local gate to a state](apply-gate.md)
- [Well-formed quantum gate](qgate-well-formed.md)
- [Applying a quantum circuit to a state](apply-circuit.md)
- [Acceptance probability of a quantum state](accept-prob.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §2.1.2 (quantum circuits as products of unitary gates; background). <https://arxiv.org/pdf/1907.09415v6>
