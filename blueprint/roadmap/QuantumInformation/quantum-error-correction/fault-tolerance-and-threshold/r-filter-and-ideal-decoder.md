# The $r$-filter and the ideal decoder

Fix an $[[n, 1, 2t + 1]]$ stabilizer code. For $r \ge 0$ the *$r$-filter* is the orthogonal projector onto the span of all
states $Q|\psi\rangle$ with $|\psi\rangle$ a codeword and $Q$ a Pauli error of
[weight](../distance-of-a-quantum-code/pauli-weight.md) at most $r$: the states that a codeword can reach with at most $r$
single-qubit errors, without regard to which codeword. The *ideal decoder* maps the $n$-qubit block to one qubit by an
error-correcting decoding circuit with no faulty locations. A state passing the $r$-filter "has at most $r$ errors", and the
ideal decoder reads off its logical state; these two maps, applied to each block, express the definitions of fault-tolerant
gadgets as equalities between circuits.

## Depends on

- [Weight of a Pauli operator](../distance-of-a-quantum-code/pauli-weight.md)
- [Stabilizer groups and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.2, Definition 1 and the discussion after it.
