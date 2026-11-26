# The quantum Hamming bound

Let $Q$ be an $[[n, k, d]]$ code and $t \ge 0$ with $2t + 1 \le d$, and let $\mathcal{E}_t$ be the set of Pauli
operators $P_1 \otimes \dots \otimes P_n$, $P_i \in \{I, X, Y, Z\}$, with at most $t$ factors different from $I$. If $Q$ is
[nondegenerate](../distance-of-a-quantum-code/degenerate-quantum-code.md) for $\mathcal{E}_t$, then

$$\sum_{j=0}^{t} 3^j \binom{n}{j} \;\le\; 2^{n-k}.$$

The left side is $|\mathcal{E}_t|$: there are $\binom{n}{j}$ ways to choose $j$ affected qubits and $3^j$ choices of
nontrivial factors. Proof: the errors in $\mathcal{E}_t$ satisfy the Knill–Laflamme conditions, since products of two of
them have weight at most $2t < d$; nondegeneracy makes the $|\mathcal{E}_t| \cdot 2^k$ vectors $E |\bar\imath\rangle$
linearly independent, and they lie in a space of dimension $2^n$. This counting proof requires nondegeneracy; for degenerate codes
see [the page on degenerate codes](degenerate-codes-and-the-quantum-hamming-bound.md). For $k = t = 1$ it reads $1 + 3n \le 2^{n-1}$, which first holds at $n = 5$, with equality.

## Depends on

- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)
- [Degenerate quantum code](../distance-of-a-quantum-code/degenerate-quantum-code.md)
- [Weight of a Pauli operator](../distance-of-a-quantum-code/pauli-weight.md)

## Proof depends on

- [The Knill–Laflamme conditions](../knill-laflamme-conditions/is-correctable-iff-knill-laflamme.md)
- [A code of distance $2t + 1$ corrects $t$ errors](../distance-of-a-quantum-code/is-correctable-of-has-distance-at-least.md)

## Background

- [Hamming sphere-packing bound](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/hamming-sphere-packing-bound.md)

## Related topics

- [Degenerate codes and the quantum Hamming bound](degenerate-codes-and-the-quantum-hamming-bound.md): what is known for degenerate codes.

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 7.1, equation (7.1).
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.8.1, equations (7.99)–(7.101).
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.2, equation (35) and Theorem 4.
