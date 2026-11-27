# Universal gate sets

A universal gate set approximates every unitary up to phase. The Hadamard and $T$ gates approximate every single-qubit
unitary, so the Clifford gates together with $T$ are universal; this is the gate set of most fault-tolerant schemes. The
Solovay–Kitaev theorem makes the approximation efficient: for gates of a fixed width, accuracy $\varepsilon$ costs only
polylogarithmically many gates in $1/\varepsilon$, and its key step is the approximation of group commutators.

- [Instruction set for $SU(d)$](instruction-set.md)
- [Universal gate set](universal-gate-set.md)
- [$H$ and $T$ approximate every single-qubit unitary](h-and-t-approximate-every-single-qubit-unitary.md)
- [Clifford plus $T$ is universal](clifford-plus-t-is-universal.md)
- [Approximating a group commutator](approximating-a-group-commutator.md)
- [The Solovay–Kitaev theorem](solovay-kitaev-theorem.md)

## Related topics

- [Exact universality of CNOT and single-qubit gates](../../quantum-foundations/exact-universality-of-cnot-and-single-qubit-gates.md): every unitary is exactly a product of CNOT and single-qubit gates.

## Sources

- P. O. Boykin, T. Mor, M. Pulver, V. Roychowdhury and F. Vatan, *A new universal and fault-tolerant quantum basis*, Inform. Process. Lett. 75 (2000), 101–107, arXiv:quant-ph/9906054v1.
- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030.
