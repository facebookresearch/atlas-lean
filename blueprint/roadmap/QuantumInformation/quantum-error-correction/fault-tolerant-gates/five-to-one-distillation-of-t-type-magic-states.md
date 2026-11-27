# Five-to-one distillation of $T$-type magic states

Let $|T_0\rangle$ be the $T$-type [magic state](magic-state.md), the eigenvector of the order-three Clifford unitary
$T$ that cycles $X \to Y \to Z$ with Bloch vector $(1, 1, 1)/\sqrt{3}$, let $|T_1\rangle$ be the orthogonal eigenvector, and
let $\rho = (1 - \varepsilon) |T_0\rangle\langle T_0| + \varepsilon |T_1\rangle\langle T_1|$ with $0 \le \varepsilon \le 1/2$; Bravyi and
Kitaev first bring the input to this form, twirling it to be diagonal in the $T$ eigenbasis and choosing the eigenvector
it is closer to as $|T_0\rangle$. Bravyi and Kitaev's subroutine
measures the four stabilizer generators of the [five-qubit code](../small-stabilizer-codes/five-qubit-code.md) on
$\rho^{\otimes 5}$, accepts on the trivial syndrome, decodes, and applies a Clifford gate swapping $|T_0\rangle$ and
$|T_1\rangle$. The transversal $T^{\otimes 5}$ preserves the code and acts on it as the logical $T$. With
$t = \varepsilon / (1 - \varepsilon)$ it accepts with probability

$$p_s = \frac{\varepsilon^5 + 5 \varepsilon^2 (1 - \varepsilon)^3 + 5 \varepsilon^3 (1 - \varepsilon)^2 + (1 - \varepsilon)^5}{6}$$

and outputs $(1 - \varepsilon_{\mathrm{out}}) |T_0\rangle\langle T_0| + \varepsilon_{\mathrm{out}} |T_1\rangle\langle T_1|$ with

$$\varepsilon_{\mathrm{out}} = \frac{t^5 + 5 t^2}{1 + 5 t^2 + 5 t^3 + t^5} \approx 5 \varepsilon^2 .$$

On $[0, 1/2]$ the equation $\varepsilon_{\mathrm{out}}(\varepsilon) = \varepsilon$ has the solutions $0$, $1/2$ and the threshold
$\varepsilon_0 = \tfrac12 \big( 1 - \sqrt{3/7} \big) \approx 0.173$; for $\varepsilon < \varepsilon_0$ iteration converges to
$|T_0\rangle$, and for $\varepsilon_0 < \varepsilon \le 1/2$ to the maximally mixed state $\varepsilon = 1/2$. The range matters:
the map commutes with $\varepsilon \mapsto 1 - \varepsilon$, so $1 - \varepsilon_0 \approx 0.827$ is a further fixed point.

## Depends on

- [Magic states](magic-state.md)
- [The five-qubit code](../small-stabilizer-codes/five-qubit-code.md)

## Sources

- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025, Section V, equations (11)–(23), the threshold $\epsilon_0$ and Appendix A.
