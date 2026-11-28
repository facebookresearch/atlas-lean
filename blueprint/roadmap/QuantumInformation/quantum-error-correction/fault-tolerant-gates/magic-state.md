# Magic states

The magic state used to implement the gate $T = \operatorname{diag}(1, e^{i\pi/4})$ is the one-qubit state

$$|A\rangle = T H |0\rangle = \tfrac{1}{\sqrt 2}\big(|0\rangle + e^{i\pi/4}|1\rangle\big),$$

the state $|A_\theta\rangle = 2^{-1/2}(|0\rangle + e^{i\theta}|1\rangle)$ of Bravyi and Kitaev with $\theta = \pi/4$.

Bravyi and Kitaev define two families. Let $|H\rangle = \cos(\pi/8)|0\rangle + \sin(\pi/8)|1\rangle$ and let
$|T_{\mathrm{BK}}\rangle$ be a unit vector with Bloch vector $\tfrac{1}{\sqrt 3}(1, 1, 1)$, so that $|H\rangle$ has Bloch vector
$\tfrac{1}{\sqrt 2}(1, 0, 1)$:
$|H\rangle\langle H| = \tfrac12 \big(I + \tfrac{1}{\sqrt 2}(X + Z)\big)$ and
$|T_{\mathrm{BK}}\rangle\langle T_{\mathrm{BK}}| = \tfrac12 \big(I + \tfrac{1}{\sqrt 3}(X + Y + Z)\big)$. Their images under one-qubit
Clifford unitaries are the magic states of $H$-type (twelve up to phase) and of $T$-type (eight up to phase); these
families are sets of states, so they do not depend on the phase chosen for each vector. The state
$|A\rangle$ is of $H$-type: $H S |H\rangle = e^{i\pi/8} |A_{-\pi/4}\rangle$, and $X |A_{-\pi/4}\rangle = e^{-i\pi/4}|A\rangle$.

## Depends on

- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)
- [The Clifford group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/clifford-group-on-n-qubits.md)

## Sources

- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025, Section I, Definition 1, and Section III, equations (2)–(4).
- P. O. Boykin, T. Mor, M. Pulver, V. Roychowdhury and F. Vatan, *A new universal and fault-tolerant quantum basis*, Inform. Process. Lett. 75 (2000), 101–107, arXiv:quant-ph/9906054v1 (titled there "On universal and fault-tolerant quantum computing"; equation and figure numbers of that version), Section 4, equation (15) ($|\varphi_0\rangle = \sigma_z^{1/4} H |0\rangle$).
