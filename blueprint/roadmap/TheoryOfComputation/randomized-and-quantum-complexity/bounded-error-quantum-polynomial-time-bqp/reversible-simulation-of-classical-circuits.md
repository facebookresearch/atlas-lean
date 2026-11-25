# Reversible simulation of classical circuits

Let $f : \{0,1\}^n \to \{0,1\}^m$ be computed by a Boolean circuit with $s$ gates (fan-in at most two). There is a circuit of
Toffoli, CNOT and NOT gates with $O(s + m)$ gates and $O(s)$ ancilla bits that maps $\lvert x, 0, y \rangle$ to
$\lvert x, 0, y \oplus f(x) \rangle$ for all $x$ and $y$, returning every ancilla to $0$: compute all gate values into ancillas,
copy the $m$ outputs into $y$ with CNOT gates, and uncompute. The term $m$ is needed: even a circuit with no gates
whose outputs are input wires requires $m$ copies into $y$. As unitaries these circuits are permutation matrices, so
quantum circuits simulate classical circuits with the same overhead.

## Depends on

- [Unitary evolution and elementary gates](../../../QuantumInformation/quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Sources

- Quantum Computing: Lecture Notes (arXiv:1907.09415v6) — Ronald de Wolf, QuSoft/CWI and University of Amsterdam (open lecture notes, arXiv), Sections 2.1 (Toffoli gates are complete for classical reversible computation) and 2.3 (a Toffoli-only circuit computing $\lvert x \rangle \lvert 0 \rangle \mapsto \lvert x \rangle \lvert f(x) \rangle$). <https://arxiv.org/abs/1907.09415v6> Background reference.
- 6.845 Lecture 4: BQP and classical friends — MIT OpenCourseWare; Scott Aaronson (scribe notes). <https://old.ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-845-quantum-complexity-theory-fall-2010/lecture-notes/MIT6_845F10_lec04.pdf> Background reference.
