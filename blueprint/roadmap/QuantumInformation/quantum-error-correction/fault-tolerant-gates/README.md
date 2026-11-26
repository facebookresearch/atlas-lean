# Fault-tolerant gates

Gates on encoded data must not spread one fault into several errors in a block. Transversal gates, which act qubit by
qubit across blocks, have this property: among stabilizer codes, bitwise CNOT preserves two identical blocks exactly for
CSS codes, and Steane's code has all Clifford gates transversal. The Eastin–Knill theorem shows that no code that detects single-qubit errors has a universal
transversal gate set, so a non-Clifford gate is added through magic states: one copy of the magic state $|A\rangle$, Clifford
gates and a measurement implement $T$ exactly up to a global phase, and noisy magic states whose fidelity exceeds the distillation thresholds can
be distilled, while mixtures of stabilizer states give no advantage.

- [Transversal gate](transversal-gate.md)
- [Transversal CNOT and CSS codes](transversal-cnot-and-css-codes.md)
- [Steane's code has transversal Clifford gates](steane-code-has-transversal-clifford-gates.md)
- [The Eastin–Knill theorem](eastin-knill-theorem.md)
- [Magic states](magic-state.md)
- [Magic-state injection](magic-state-injection.md)
- [Clifford operations with magic states are universal](clifford-operations-with-magic-states-are-universal.md)
- [Clifford computations with mixtures of stabilizer states are classically simulable](mixtures-of-stabilizer-states-give-no-quantum-advantage.md)
- [Magic-state distillation](magic-state-distillation.md)

## Related topics

- [Clifford group](../clifford-group/README.md): the gates that stabilizer codes implement most easily.
- [Universal gate sets](../universal-gate-sets/README.md): Clifford plus $T$.

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Chapter 5.
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.
- B. Eastin and E. Knill, *Restrictions on transversal encoded quantum gate sets*, Phys. Rev. Lett. 102 (2009), 110502, arXiv:0811.4262.
- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025.
