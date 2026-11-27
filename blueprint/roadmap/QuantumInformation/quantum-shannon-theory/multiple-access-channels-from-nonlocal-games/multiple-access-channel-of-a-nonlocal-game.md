# Multiple access channel of a nonlocal game and its entanglement-assisted rate region

A nonlocal game turns into a classical two-sender multiple access channel: each sender inputs a question and an answer of one player, and the channel reveals the question pair when the answers win and outputs a uniformly random question pair otherwise. Senders sharing finite-dimensional entanglement reach rate pairs that form the entanglement-assisted achievable rate region.

**The channel of a game.** Let $G = (\mathcal{X}_1, \mathcal{X}_2, \mathcal{Y}_1, \mathcal{Y}_2, W)$ be a promise-free two-player [nonlocal game](../../quantum-foundations/two-player-nonlocal-games-classical-and-entangled-values.md), with finite question sets $\mathcal{X}_i$, answer sets $\mathcal{Y}_i$ and winning set $W \subseteq \mathcal{X}_1 \times \mathcal{X}_2 \times \mathcal{Y}_1 \times \mathcal{Y}_2$. (A game with a promise $P \subsetneq \mathcal{X}_1 \times \mathcal{X}_2$ becomes promise-free when every question pair outside $P$ is declared winning.) The [multiple access channel](../../../InformationTheory/channel-coding/two-user-discrete-memoryless-multiple-access-channel-and-its.md) $N_G : (\mathcal{X}_1 \times \mathcal{Y}_1) \times (\mathcal{X}_2 \times \mathcal{Y}_2) \to \mathcal{X}_1 \times \mathcal{X}_2$ is

$$
N_G(\hat{x}_1, \hat{x}_2 \mid x_1, y_1; x_2, y_2) = \begin{cases} \delta_{x_1 \hat{x}_1}\, \delta_{x_2 \hat{x}_2} & \text{if } (x_1, x_2, y_1, y_2) \in W, \\ (\lvert\mathcal{X}_1\rvert\, \lvert\mathcal{X}_2\rvert)^{-1} & \text{otherwise.} \end{cases}
$$

**Entanglement-assisted region.** For a classical multiple access channel $N$ with input alphabets $\mathcal{A}, \mathcal{B}$ and capacity region $\mathcal{C}(N)$, the *$d$-entanglement-assisted achievable rate region* is

$$
\mathcal{C}^{(1)}_{\mathrm{EA},d}(N) = \bigcup_{E} \mathcal{C}(N \circ E).
$$

The union is over all classical channels $E(a, b \mid a_1, b_1) = \sum_{a_2, b_2} f_1(a \mid a_1, a_2)\, f_2(b \mid b_1, b_2)\, \langle\psi\rvert L^{(a_1)}_{a_2} \otimes M^{(b_1)}_{b_2} \lvert\psi\rangle$ built from: a state $\lvert\psi\rangle \in \mathbb{C}^d \otimes \mathbb{C}^d$; finite alphabets $\mathcal{A}_1, \mathcal{B}_1, \mathcal{A}_2, \mathcal{B}_2$; POVMs $\{L^{(a_1)}_{a_2}\}_{a_2}$ and $\{M^{(b_1)}_{b_2}\}_{b_2}$ on $\mathbb{C}^d$; and post-processings $f_1 : \mathcal{A}_1 \times \mathcal{A}_2 \to \mathcal{A}$ and $f_2 : \mathcal{B}_1 \times \mathcal{B}_2 \to \mathcal{B}$. Here $N \circ E$ is a multiple access channel with inputs $\mathcal{A}_1 \times \mathcal{B}_1$. The *entanglement-assisted achievable rate region* is $\mathcal{C}^{(1)}_{\mathrm{EA}}(N) = \bigcup_{d \in \mathbb{N}} \mathcal{C}^{(1)}_{\mathrm{EA},d}(N)$, which allows entanglement of arbitrarily large but finite local dimension.

## Depends on

- [Two-player nonlocal games: classical and entangled values](../../quantum-foundations/two-player-nonlocal-games-classical-and-entangled-values.md)
- [Two-user discrete memoryless multiple-access channel and its capacity region](../../../InformationTheory/channel-coding/two-user-discrete-memoryless-multiple-access-channel-and-its.md)
- [Density matrices, pure states and reduced states](../../../QuantumInformation/quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Positive-operator-valued measurements and the Born rule](../../../QuantumInformation/quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)

## Proof depends on

None.

## Expansion

For a game whose question sets have sizes $m = \lvert\mathcal{X}_1\rvert$ and $n = \lvert\mathcal{X}_2\rvert$, the output of $N_G$ carries at most $\log m + \log n$ bits, so $(\log m, \log n)$ is the largest conceivable rate pair. Senders who win the game with certainty, choosing questions uniformly at random and answering with a perfect strategy, reach it. If no finite-dimensional entangled strategy wins with certainty, then for every finite $d$ the achievable sum rate is bounded away from $\log m + \log n$. For the channel of the magic square game, entanglement shared between the senders strictly enlarges the achievable rates beyond the unassisted capacity region. By the coding theorem for classical multiple access channels, every point of $\mathcal{C}^{(1)}_{\mathrm{EA},d}(N)$ is achievable with $d$-dimensional entanglement.

## Sources

- F. Leditzky, M. A. Alhejji, J. Levin and G. Smith, "Playing games with multiple access channels", *Nature Communications* 11, article 1497, 2020, doi:[10.1038/s41467-020-15240-w](https://doi.org/10.1038/s41467-020-15240-w). Numbering of the version read, arXiv:1909.02479v2: Appendix A (nonlocal games, promise-free games, capacity regions of multiple access channels and entanglement assistance, including the definitions of the $d$-entanglement-assisted and entanglement-assisted achievable rate regions) and Appendix B (the channel $N_G$).
