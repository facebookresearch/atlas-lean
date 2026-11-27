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
- [Euler decomposition of single-qubit unitaries](euler-decomposition-of-single-qubit-unitaries.md)
- [The $ABC$ decomposition of a special unitary matrix](abc-decomposition-of-special-unitary-matrices.md)
- [A controlled single-qubit unitary from two CNOTs and four single-qubit gates](controlled-unitary-from-two-cnots-and-single-qubit-gates.md)
- [A doubly controlled unitary from controlled square roots](doubly-controlled-unitary-from-a-square-root.md)
- [A multiply controlled NOT from Toffoli gates with one borrowed qubit](multiply-controlled-not-with-one-borrowed-qubit.md)
- [Multiply controlled unitaries from CNOT and single-qubit gates](multiply-controlled-unitary-from-cnot-and-single-qubit-gates.md)
- [Decomposition of a unitary into two-level unitaries](decomposition-into-two-level-unitaries.md)
- [A diagonal unitary is a product of two-level diagonal unitaries](diagonal-unitary-as-a-product-of-two-level-unitaries.md)
- [A two-level unitary from multiply controlled gates along a Gray code](two-level-unitary-from-multiply-controlled-gates-along-a-gray-code.md)
- [A traceless Hermitian matrix is a commutator of small Hermitian matrices](traceless-hermitian-matrix-as-a-commutator.md)
- [The group commutator of exponentials approximates the exponential of the commutator](group-commutator-of-exponentials-approximates-the-exponential-of-the-commutator.md)
- [Approximate balanced group commutators in $SU(d)$](approximate-balanced-group-commutators-in-sud.md)
- [Finite nets from an instruction set](epsilon-nets-from-an-instruction-set.md)
- [The Solovay–Kitaev recursion step](solovay-kitaev-recursion-step.md)
- [The Solovay–Kitaev theorem](solovay-kitaev-theorem.md)

## Related topics

- [Exact universality of CNOT and single-qubit gates](../../quantum-foundations/exact-universality-of-cnot-and-single-qubit-gates.md): every unitary is exactly a product of CNOT and single-qubit gates.

## Sources

- P. O. Boykin, T. Mor, M. Pulver, V. Roychowdhury and F. Vatan, *A new universal and fault-tolerant quantum basis*, Inform. Process. Lett. 75 (2000), 101–107, arXiv:quant-ph/9906054v1.
- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030.
