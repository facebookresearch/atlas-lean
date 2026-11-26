# Clifford plus $T$ is universal

The set $\{H, T, \mathrm{CNOT}\}$, with $T = \operatorname{diag}(1, e^{i\pi/4})$, is a
[universal gate set](universal-gate-set.md). Since $S = T^2$, so is the set of the Clifford gates $H$, $S$, CNOT together
with $T$. By contrast the Clifford gates alone are [not universal](../clifford-group/clifford-gates-are-not-universal.md).

Proof: every unitary on $n$ qubits is exactly a product of single-qubit unitaries and CNOT gates
([exact universality](../../quantum-foundations/exact-universality-of-cnot-and-single-qubit-gates.md)), and every
single-qubit unitary is approximated up to phase by products of $H$ and $T$
([density](h-and-t-approximate-every-single-qubit-unitary.md)); errors add up at most linearly along a product of
unitaries.

## Depends on

- [Universal gate set](universal-gate-set.md)
- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Proof depends on

- [Exact universality of CNOT and single-qubit gates](../../quantum-foundations/exact-universality-of-cnot-and-single-qubit-gates.md)
- [$H$ and $T$ approximate every single-qubit unitary](h-and-t-approximate-every-single-qubit-unitary.md)
- [Telescoping bound for products of contractions](../../not-yet-classified/part-01/unitary-error-budget/norm-list-of-fn-prod-sub-le.md)

## Background

- [Clifford gates are not universal](../clifford-group/clifford-gates-are-not-universal.md)

## Sources

- P. O. Boykin, T. Mor, M. Pulver, V. Roychowdhury and F. Vatan, *A new universal and fault-tolerant quantum basis*, Inform. Process. Lett. 75 (2000), 101–107, arXiv:quant-ph/9906054v1 (section, equation and appendix numbers of that version), Abstract and Section 3.
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.5 ("the Clifford group plus $R_{\pi/8}$ form a universal set of gates").
