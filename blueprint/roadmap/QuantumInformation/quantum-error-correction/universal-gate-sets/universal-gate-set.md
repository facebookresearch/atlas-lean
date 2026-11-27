# Universal gate set

A finite set $\mathcal{G}$ of quantum gates, each a unitary on a fixed number of qubits, is universal if for every
$n$ at least the largest number of qubits of a gate in $\mathcal{G}$, every unitary $U$ on $n$ qubits and every
$\varepsilon > 0$, there are a finite product $V = G_1 \cdots G_m$, where each $G_j$ is a gate of $\mathcal{G}$ applied
to an ordered tuple of distinct qubits and tensored with the identity on the rest, and a phase $\theta \in \mathbb{R}$,
such that

$$\| U - e^{i\theta} V \| < \varepsilon$$

in the operator norm. Global phases are ignored because they have no physical effect. The infinite set of all
single-qubit unitaries together with CNOT is not a gate set in this sense; it generates every unitary exactly, a separate
statement ([exact universality](../../quantum-foundations/exact-universality-of-cnot-and-single-qubit-gates.md)).

## Depends on

- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Background

- [Exact universality of CNOT and single-qubit gates](../../quantum-foundations/exact-universality-of-cnot-and-single-qubit-gates.md)

## Sources

- P. O. Boykin, T. Mor, M. Pulver, V. Roychowdhury and F. Vatan, *A new universal and fault-tolerant quantum basis*, Inform. Process. Lett. 75 (2000), 101–107, arXiv:quant-ph/9906054v1 (section, equation and appendix numbers of that version), Sections 1 and 3 (universality as approximation to any desired precision).
- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 2 (approximation in operator norm).
