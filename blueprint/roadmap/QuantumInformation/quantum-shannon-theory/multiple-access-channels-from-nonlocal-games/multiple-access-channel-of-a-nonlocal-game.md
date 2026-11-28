# Multiple access channel of a nonlocal game

A nonlocal game turns into a classical two-sender multiple access channel: each sender inputs a question and an answer of one player, and the channel reveals the question pair when the answers win and outputs a uniformly random question pair otherwise.

**The channel of a game.** Let $G = (\mathcal{X}_1, \mathcal{X}_2, \mathcal{Y}_1, \mathcal{Y}_2, W)$ be a promise-free two-player [nonlocal game](../../quantum-foundations/two-player-nonlocal-games-classical-and-entangled-values.md), with finite question sets $\mathcal{X}_i$, answer sets $\mathcal{Y}_i$ and winning set $W \subseteq \mathcal{X}_1 \times \mathcal{X}_2 \times \mathcal{Y}_1 \times \mathcal{Y}_2$. (A game with a promise $P \subsetneq \mathcal{X}_1 \times \mathcal{X}_2$ becomes promise-free when every question pair outside $P$ is declared winning.) The [multiple access channel](../../../InformationTheory/channel-coding/two-user-discrete-memoryless-multiple-access-channel-and-its.md) $N_G : (\mathcal{X}_1 \times \mathcal{Y}_1) \times (\mathcal{X}_2 \times \mathcal{Y}_2) \to \mathcal{X}_1 \times \mathcal{X}_2$ is

$$
N_G(\hat{x}_1, \hat{x}_2 \mid x_1, y_1; x_2, y_2) = \begin{cases} \delta_{x_1 \hat{x}_1}\, \delta_{x_2 \hat{x}_2} & \text{if } (x_1, x_2, y_1, y_2) \in W, \\ (\lvert\mathcal{X}_1\rvert\, \lvert\mathcal{X}_2\rvert)^{-1} & \text{otherwise.} \end{cases}
$$

## Depends on

- [Two-player nonlocal games: classical and entangled values](../../quantum-foundations/two-player-nonlocal-games-classical-and-entangled-values.md)
- [Two-user discrete memoryless multiple-access channel and its capacity region](../../../InformationTheory/channel-coding/two-user-discrete-memoryless-multiple-access-channel-and-its.md)

## Proof depends on

None.

## Remarks

For a game whose question sets have sizes $m = \lvert\mathcal{X}_1\rvert$ and $n = \lvert\mathcal{X}_2\rvert$, the output of $N_G$ carries at most $\log m + \log n$ bits, so $(\log m, \log n)$ is the largest conceivable rate pair. Senders who win the game with certainty, choosing questions uniformly at random and answering with a perfect strategy, reach it; senders sharing entanglement reach the rate pairs of the [entanglement-assisted rate region](entanglement-assisted-rate-region-of-a-multiple-access-channel.md). If a game has no perfect classical strategy, or none of a fixed local dimension $d$, the sum rate reachable with those resources is bounded away from $\log m + \log n$, by a gap that may depend on $d$ (Theorem 1 and Proposition 3 of the source); with entanglement of unbounded finite dimension it need not be, as the game of Slofstra and Vidick shows (Corollary 7 of the source); for the channel of the magic square game this separates the unassisted capacity region from the point $(\log 3, \log 3)$, which senders sharing entanglement reach with the perfect quantum strategy (Section 2.1 and Appendix C of the source).

## Sources

- F. Leditzky, M. A. Alhejji, J. Levin and G. Smith, "Playing games with multiple access channels", *Nature Communications* 11, article 1497, 2020, doi:[10.1038/s41467-020-15240-w](https://doi.org/10.1038/s41467-020-15240-w). Numbering of the version read, arXiv:1909.02479v2: Appendix A (nonlocal games and promise-free games), Appendix B (the channel $N_G$), Theorem 1, Section 2.1 and Proposition 3 (the sum rate bound for games without a perfect strategy and the magic square example), Corollary 7 (the game of Slofstra and Vidick) and Appendix C (the magic square game and its channel).
