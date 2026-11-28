# Entanglement-assisted rate region of a multiple access channel

The entanglement-assisted achievable rate region of a classical two-sender multiple access channel collects the rate pairs that senders can reach when they share an entangled state of some finite local dimension and use measurement outcomes on it, together with their messages, to choose the channel inputs.

**Definition.** For a classical [multiple access channel](../../../InformationTheory/channel-coding/two-user-discrete-memoryless-multiple-access-channel-and-its.md) $N$ with input alphabets $\mathcal{A}, \mathcal{B}$ and capacity region $\mathcal{C}(N)$, the *$d$-entanglement-assisted achievable rate region* is

$$
\mathcal{C}^{(1)}_{\mathrm{EA},d}(N) = \bigcup_{E} \mathcal{C}(N \circ E).
$$

The union is over all classical channels $E(a, b \mid a_1, b_1) = \sum_{a_2, b_2} f_1(a \mid a_1, a_2)\, f_2(b \mid b_1, b_2)\, \langle\psi\rvert L^{(a_1)}_{a_2} \otimes M^{(b_1)}_{b_2} \lvert\psi\rangle$ built from: a unit vector, a [pure state](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md), $\lvert\psi\rangle \in \mathbb{C}^d \otimes \mathbb{C}^d$ with $d \ge 1$; finite alphabets $\mathcal{A}_1, \mathcal{B}_1, \mathcal{A}_2, \mathcal{B}_2$; [POVMs](../../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md) $\{L^{(a_1)}_{a_2}\}_{a_2}$ and $\{M^{(b_1)}_{b_2}\}_{b_2}$ on $\mathbb{C}^d$; and post-processings $f_1 : \mathcal{A}_1 \times \mathcal{A}_2 \to \mathcal{A}$ and $f_2 : \mathcal{B}_1 \times \mathcal{B}_2 \to \mathcal{B}$, written in the formula as $f_1(a \mid a_1, a_2) = 1$ if $f_1(a_1, a_2) = a$ and $0$ otherwise, and likewise for $f_2$. With the senders drawing $a_1$ and $b_1$ independently, $N \circ E$ is a multiple access channel with input alphabets $\mathcal{A}_1$ and $\mathcal{B}_1$, and $\mathcal{C}(N \circ E)$ is its capacity region. The *entanglement-assisted achievable rate region* is

$$
\mathcal{C}^{(1)}_{\mathrm{EA}}(N) = \bigcup_{d \in \mathbb{N}} \mathcal{C}^{(1)}_{\mathrm{EA},d}(N),
$$

which allows entanglement of arbitrarily large but finite local dimension; it is the union, not its closure.

## Depends on

- [Two-user discrete memoryless multiple-access channel and its capacity region](../../../InformationTheory/channel-coding/two-user-discrete-memoryless-multiple-access-channel-and-its.md)
- [Density matrices, pure states and reduced states](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Positive-operator-valued measurements and the Born rule](../../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)

## Proof depends on

None.

## Remarks

By the coding theorem for classical multiple access channels, every point of $\mathcal{C}^{(1)}_{\mathrm{EA},d}(N)$ is achievable with $d$-dimensional entanglement.

## Sources

- F. Leditzky, M. A. Alhejji, J. Levin and G. Smith, "Playing games with multiple access channels", *Nature Communications* 11, article 1497, 2020, doi:[10.1038/s41467-020-15240-w](https://doi.org/10.1038/s41467-020-15240-w). Numbering of the version read, arXiv:1909.02479v2: Appendix A.2 (capacity regions of multiple access channels, Equation (6)) and Appendix A.3 (entanglement assistance, Equations (7)–(10), and the definitions of the $d$-entanglement-assisted and entanglement-assisted achievable rate regions, Equations (11) and (14)).
