# Magic-state distillation

Bravyi and Kitaev's distillation theorems: in the model of Clifford unitaries, preparation of $|0\rangle$, one-qubit Pauli
measurements and adaptive control, with independent copies of a noisy one-qubit state $\rho$, universal quantum
computation can be simulated efficiently whenever

- $F_T(\rho) = \max_{U} \langle T_{\mathrm{BK}} | U^{*} \rho U | T_{\mathrm{BK}} \rangle^{1/2} > F_T = \big(\tfrac12 (1 + \sqrt{3/7})\big)^{1/2} \approx 0.910$,
  the maximum taken over one-qubit Clifford unitaries $U$ (Theorem 2), or
- $F_H(\rho) = \max_{U} \langle H | U^{*} \rho U | H \rangle^{1/2}$ exceeds a constant $F_H \approx 0.927$ (Theorem 3).

The protocols consume several copies of $\rho$ and output one copy closer to a [magic state](magic-state.md). The
$H$-type protocol uses the [fifteen-qubit code](../small-stabilizer-codes/fifteen-qubit-quantum-reed-muller-code.md) and
its [transversal $T$](../small-stabilizer-codes/transversal-t-preserves-the-fifteen-qubit-code.md); after aligning and
dephasing the input so that it has error $\varepsilon = 1 - F_H(\rho)^2$, one round accepts with probability
$p_s = (1 + 15(1 - 2\varepsilon)^8)/16$, which tends to $1$ only as $\varepsilon \to 0$ (it is about $0.22$ at $\varepsilon = 0.1$),
and the accepted output has error $\varepsilon_{\mathrm{out}} = 35 \varepsilon^3 + O(\varepsilon^4)$.
States inside the stabilizer octahedron give no advantage, and $F_T$ cannot be lowered below
$F_T^{*} = \big(\tfrac12(1 + \sqrt{1/3})\big)^{1/2} \approx 0.888$.

## Expansion

This node is a family. The iteration uses the success probabilities, output errors and thresholds of the five-qubit and
fifteen-qubit subroutines (linked below); a good expansion adds a page for the error analysis of Bravyi and Kitaev's Section IV, which
iterates a subroutine, counts the raw magic states used (on the order of $(\log(1/\varepsilon_{\mathrm{out}}))^{\gamma}$
with $\gamma = \log_3 15$ for the fifteen-qubit scheme) and combines the distilled states with
[magic-state injection](magic-state-injection.md) to simulate a universal circuit.

## Depends on

- [Magic states](magic-state.md)
- [The fifteen-qubit quantum Reed–Muller code](../small-stabilizer-codes/fifteen-qubit-quantum-reed-muller-code.md)
- [Transversal $T$ preserves the fifteen-qubit code](../small-stabilizer-codes/transversal-t-preserves-the-fifteen-qubit-code.md)

## Proof depends on

- [Five-to-one distillation of $T$-type magic states](five-to-one-distillation-of-t-type-magic-states.md)
- [Fifteen-to-one distillation of $H$-type magic states](fifteen-to-one-distillation-of-h-type-magic-states.md)

## Background

- [Clifford computations with mixtures of stabilizer states are classically simulable](mixtures-of-stabilizer-states-give-no-quantum-advantage.md)

## Sources

- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025, Section I, Theorems 2 and 3, and Sections IV–VI, equations (5)–(6) and (38)–(39).
