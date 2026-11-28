# The $r$-filter and the ideal decoder

Fix an $[[n, 1, 2t + 1]]$ code, not necessarily a stabilizer code. For $r \ge 0$ the *$r$-filter* is the orthogonal projector onto the span of all
states $Q|\psi\rangle$ with $|\psi\rangle$ a codeword and $Q$ a Pauli error of
[weight](../distance-of-a-quantum-code/pauli-weight.md) at most $r$, the span of the states reachable from codewords by errors of weight at most $r$. The *ideal decoder* maps the $n$-qubit block to one qubit by a fixed
error-correcting decoding circuit with no faulty locations, which takes every state $Q|\bar\psi\rangle$, for a codeword
$|\bar\psi\rangle$ encoding $|\psi\rangle$ and a Pauli error $Q$ of weight at most $t$, to $|\psi\rangle$ on the output qubit;
it exists because the code corrects every error of weight at most $t$ (Gottesman, Section 4.2, Definition 1). By convention a state passing the $r$-filter "has at most $r$ errors"; this is
not a statement about how it arose, since the span contains sums of terms reached from different codewords that no single
codeword reaches by one such error (for the five-qubit code with an extra qubit in $|0\rangle$, a $[[6, 1, 3]]$ code, the
normalized sum of $|\bar 0\rangle|0\rangle$ and $|\bar 1\rangle|1\rangle$ passes the $1$-filter but is entangled across the extra
qubit, while every codeword is a product there). The ideal decoder reads off the logical state of a state passing the
$t$-filter; these two maps, applied to each block, express the definitions of fault-tolerant
gadgets as equalities between circuits.

## Depends on

- [Weight of a Pauli operator](../distance-of-a-quantum-code/pauli-weight.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)

## Proof depends on

- [A code of distance $2t + 1$ corrects $t$ errors](../distance-of-a-quantum-code/is-correctable-of-has-distance-at-least.md): one recovery corrects every error of weight at most $t$

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.2, Definition 1 and the discussion after it.
