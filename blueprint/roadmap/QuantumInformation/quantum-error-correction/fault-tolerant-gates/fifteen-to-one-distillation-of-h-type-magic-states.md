# Fifteen-to-one distillation of $H$-type magic states

Let $\rho = (1 - \varepsilon) |A_0\rangle\langle A_0| + \varepsilon |A_1\rangle\langle A_1|$, where
$|A_0\rangle = (|0\rangle + e^{i\pi/4} |1\rangle)/\sqrt{2}$ is an $H$-type [magic state](magic-state.md) up to a Clifford
unitary and $|A_1\rangle = Z|A_0\rangle$; any one-qubit state can be brought to this form by Clifford operations and
twirling. Bravyi and Kitaev's subroutine takes $\rho^{\otimes 15}$, measures the syndrome of the
[fifteen-qubit code](../small-stabilizer-codes/fifteen-qubit-quantum-reed-muller-code.md) with each $X$-type stabilizer generator $X(u)$ replaced by
$A(u) = \bigotimes_{i \in u} A_i$, where $A = (X + Y)/\sqrt{2}$, a Hermitian Clifford unitary ($A X A = Y$, $A Z A = -Z$). It equals $W X W^{*}$ for
$W = \operatorname{diag}(1, e^{i\pi/4})$, which is not a Clifford unitary and is not used by the protocol. After the
$Z$-syndrome $\mu$ is measured, choose $w$ with $w \cdot v = \mu(v)$ for every $v \in L_2$ and apply the Clifford correction
$A(w)^{*}$; then ordinary $X$-type measurements read the $A$-syndrome (Bravyi and Kitaev, steps 1–4 before equation (28)). It accepts
when the $A$-syndrome is trivial, and decodes. It accepts with probability

$$p_s = \frac{1 + 15 (1 - 2\varepsilon)^8}{16} ,$$

and on acceptance outputs $(1 - \varepsilon_{\mathrm{out}}) |A_0\rangle\langle A_0| + \varepsilon_{\mathrm{out}} |A_1\rangle\langle A_1|$ with

$$\varepsilon_{\mathrm{out}} = \frac{1 - 15 (1 - 2\varepsilon)^7 + 15 (1 - 2\varepsilon)^8 - (1 - 2\varepsilon)^{15}}{2 \big( 1 + 15 (1 - 2\varepsilon)^8 \big)}
= 35 \varepsilon^3 + O(\varepsilon^4) .$$

These come from $p_s = \sum_{v \in L_1^{\perp}} \varepsilon^{15 - |v|} (1 - \varepsilon)^{|v|}$ and
$\varepsilon_{\mathrm{out}} = p_s^{-1} \sum_{v \in L_2} \varepsilon^{15 - |v|} (1 - \varepsilon)^{|v|}$ by the
MacWilliams identity and the weight enumerator $W_{L_1}(x, y) = x^{15} + 15 x^7 y^8$. Besides $0$ and $1/2$, the
equation $\varepsilon_{\mathrm{out}}(\varepsilon) = \varepsilon$ has the interior threshold solution $\varepsilon_0 \approx 0.141$ in
$(0, 1/2)$; below it, iterating the
subroutine drives the error to zero.

## Depends on

- [Magic states](magic-state.md)
- [The fifteen-qubit quantum Reed–Muller code](../small-stabilizer-codes/fifteen-qubit-quantum-reed-muller-code.md)

## Proof depends on

- [Weights in the shortened Reed–Muller codes of the fifteen-qubit code](../small-stabilizer-codes/weights-in-the-shortened-reed-muller-codes-of-the-fifteen-qubit-code.md)
- [The MacWilliams identity](../../../InformationTheory/error-correcting-codes/macwilliams-identity.md)
- [Transversal $T$ preserves the fifteen-qubit code](../small-stabilizer-codes/transversal-t-preserves-the-fifteen-qubit-code.md)

## Sources

- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025, Section VI, Lemma 2, the distillation subroutine (steps 1–6), equations (28)–(37), and equation (38) (the expansion $35\varepsilon^3$).
