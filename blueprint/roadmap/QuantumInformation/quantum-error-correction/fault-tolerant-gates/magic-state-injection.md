# Magic-state injection

Let $|\psi\rangle = a|0\rangle + b|1\rangle$ be a qubit state and $|A\rangle = \tfrac{1}{\sqrt 2}(|0\rangle + e^{i\pi/4}|1\rangle)$ the
[magic state](magic-state.md). Apply CNOT with $|\psi\rangle$ as control and $|A\rangle$ as target, then measure the target
in the computational basis. Each outcome has probability $1/2$. On outcome $0$ the control is left in $T|\psi\rangle$;
on outcome $1$ it is left in $e^{i\pi/4} T^{*} |\psi\rangle$, and applying $S = \operatorname{diag}(1, i)$ gives
$T|\psi\rangle$ up to a global phase. So one copy of $|A\rangle$, a CNOT, a computational-basis measurement and a
classically controlled $S$ implement $T$ exactly, up to a global phase.

Proof: after the CNOT the state is
$\tfrac{1}{\sqrt 2}\big[(a|0\rangle + e^{i\pi/4} b|1\rangle)|0\rangle + (e^{i\pi/4} a|0\rangle + b|1\rangle)|1\rangle\big]$; the first bracket is
$T|\psi\rangle$, the second is $e^{i\pi/4} T^{*}|\psi\rangle$, both of norm $1$, and $S T^{*} = T$.

## Depends on

- [Magic states](magic-state.md)
- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)
- [Partial measurement and the principle of deferred measurement](../../quantum-foundations/partial-measurement-and-the-principle-of-deferred-measuremen.md)

## Sources

- P. O. Boykin, T. Mor, M. Pulver, V. Roychowdhury and F. Vatan, *A new universal and fault-tolerant quantum basis*, Inform. Process. Lett. 75 (2000), 101–107, arXiv:quant-ph/9906054v1 (titled there "On universal and fault-tolerant quantum computing"; equation and figure numbers of that version), Section 4, equation (15) ($|\varphi_0\rangle = \sigma_z^{1/4} H |0\rangle$) and Figure 1.
- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025, Section III (the same circuit for $|A_\theta\rangle$, with the measurement of $Z \otimes Z$).
