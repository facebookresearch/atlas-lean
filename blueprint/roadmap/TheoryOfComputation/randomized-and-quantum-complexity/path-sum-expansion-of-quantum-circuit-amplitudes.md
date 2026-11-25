# Path-sum expansion of quantum circuit amplitudes

Let $U = U_T \cdots U_1$ be a product of $T$ unitary gates, each acting on at most two of $N$ qubits. For
computational basis states $x, y$,

$$\langle y | U | x\rangle = \sum_{z_1, \dots, z_{T-1}} \langle y | U_T | z_{T-1}\rangle \cdots
\langle z_2 | U_2 | z_1\rangle \langle z_1 | U_1 | x\rangle,$$

a sum over sequences of intermediate computational basis states $z_1, \dots, z_{T-1}$, in which each factor is an
entry of a single gate.

For circuits over a fixed finite gate set with efficiently computable entries, evaluating this sum term by term
is the argument behind
[BQP is contained in PSPACE](bounded-error-quantum-polynomial-time-bqp/bqp-subset-pspace.md); the encoding and
precision accounting belong to that page.

## Proof depends on

- [Applying a 2-local gate to a state](../complexity-classes/time-and-space-complexity-classes/apply-gate.md)

## Sources

- S. Aaronson, MIT 6.845 Quantum Complexity Theory, Lecture 4 (scribe notes), Fall 2010, §2.4. <https://old.ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-845-quantum-complexity-theory-fall-2010/lecture-notes/MIT6_845F10_lec04.pdf>
