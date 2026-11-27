# History-state completeness bound

Let $V = U_T \cdots U_1$, with $T \ge 1$, be a verifier circuit of unitary gates on a witness register and work qubits
initialized to $0$, where acceptance is outcome $1$ when an output qubit is measured in the computational basis. For a
witness state $\xi$, the history state is
$\lvert \eta \rangle = \frac{1}{\sqrt{T+1}} \sum_{t=0}^{T} U_t \cdots U_1 \lvert \xi, 0 \rangle \otimes \lvert t \rangle$, with clock states
$\lvert t \rangle$ (binary, or the legal unary states $1^t 0^{T-t}$). Let
$H = J_{\mathrm{in}} H_{\mathrm{in}} + H_{\mathrm{out}} + J_{\mathrm{prop}} H_{\mathrm{prop}} + J_{\mathrm{clock}} H_{\mathrm{clock}}$ with arbitrary weights
$J_{\mathrm{in}}, J_{\mathrm{prop}}, J_{\mathrm{clock}} \ge 0$, where
$H_{\mathrm{in}} = \sum_i \lvert 1 \rangle\langle 1 \rvert_i \otimes \lvert 0 \rangle\langle 0 \rvert$ sums over the work qubits,
$H_{\mathrm{out}} = \lvert 0 \rangle\langle 0 \rvert_{\mathrm{out}} \otimes \lvert T \rangle\langle T \rvert$ has coefficient exactly $1$,
$H_{\mathrm{prop}} = \sum_{t=1}^{T} \tfrac12 \bigl(I \otimes (\lvert t \rangle\langle t \rvert + \lvert t-1 \rangle\langle t-1 \rvert) - U_t \otimes \lvert t \rangle\langle t-1 \rvert - U_t^* \otimes \lvert t-1 \rangle\langle t \rvert\bigr)$,
and, for a unary clock, $H_{\mathrm{clock}} \succeq 0$ vanishes on legal clock states and the clock projectors above are the
corresponding local clock operators, which agree with them on legal clock states. If $V$ accepts $\xi$ with probability at
least $1 - \varepsilon$, then
$\langle \eta \rvert H \lvert \eta \rangle = (1 - \Pr[V \text{ accepts } \xi])/(T+1) \le \varepsilon/(T+1)$, since $\lvert \eta \rangle$ has energy $0$ for
$H_{\mathrm{in}}$, $H_{\mathrm{prop}}$ and $H_{\mathrm{clock}}$. With $H_{\mathrm{out}}$ scaled by $T + 1$, as in Kempe, Kitaev and Regev, the
bound becomes $\varepsilon$. The QMA-completeness of the local Hamiltonian problem uses this bound; it is not a
prerequisite of it.

## Depends on

- [Unitary evolution and elementary gates](../../QuantumInformation/quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Related topics

- [QMA for promise problems](local-hamiltonian-problem/qmapromise.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §14.3 (the Hamiltonian $H_{\mathrm{init}} + \sum_t H_t + H_{\mathrm{final}}$ with a binary clock) and §14.3.1 (the history state has energy $\frac{1}{T+1}\langle\psi_T|(|0\rangle\langle 0|_1 \otimes I)|\psi_T\rangle$). <https://arxiv.org/pdf/1907.09415v6>
- J. Kempe, A. Kitaev and O. Regev, "The complexity of the local Hamiltonian problem", arXiv:quant-ph/0406180v2, Section 4, Lemma 2 and its proof ($H_{\mathrm{out}} = (T+1)|0\rangle\langle 0|_1 \otimes |T\rangle\langle T|$, energy below $\varepsilon$) and Section 5 (unary clock and $H_{\mathrm{clock}}$). <https://arxiv.org/abs/quant-ph/0406180>
