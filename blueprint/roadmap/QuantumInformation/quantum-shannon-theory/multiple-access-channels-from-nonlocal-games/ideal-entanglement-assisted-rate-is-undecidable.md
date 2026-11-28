# Achieving the ideal rate pair with entanglement is undecidable for game channels

No algorithm decides, given a linear system over $\mathbb{F}_2$, whether senders sharing finite-dimensional entanglement can reach the ideal rate pair $(\log m, \log n)$ on the multiple access channel built from the system's nonlocal game.

**Theorem (Leditzky, Alhejji, Levin and Smith).** Let $Ax = b$ be an $m \times n$ linear system over $\mathbb{F}_2$, and let $V_i = \{j \in [n] : A_{ij} \neq 0\}$ be the variables of equation $i$. Its *linear system game* $G_{\mathrm{LS}}$ is the promise-free [nonlocal game](../../quantum-foundations/two-player-nonlocal-games-classical-and-entangled-values.md) with question sets $\mathcal{X}_1 = [m]$ and $\mathcal{X}_2 = [n]$, answer sets $\mathcal{Y}_1 = \mathbb{F}_2^n$ and $\mathcal{Y}_2 = \mathbb{F}_2$, and winning set

$$
W = \Bigl\{ (i, j, y, z) : \textstyle\sum_{k \in V_i} y_k = b_i \text{ and } \bigl(j \notin V_i \text{ or } z = y_j\bigr) \Bigr\}.
$$

Let $N_{G_{\mathrm{LS}}}$ be the [multiple access channel of this game](multiple-access-channel-of-a-nonlocal-game.md). It is undecidable to determine, given $A$ and $b$, whether the rate pair $(\log m, \log n)$ belongs to the [entanglement-assisted achievable rate region](entanglement-assisted-rate-region-of-a-multiple-access-channel.md) $\mathcal{C}^{(1)}_{\mathrm{EA}}(N_{G_{\mathrm{LS}}})$ (Proposition 8 of the source).

Every question pair is asked: Alice receives an equation $i$ and answers a full assignment $y$ satisfying it, Bob receives a variable $j$ and answers a bit, and they win automatically when $x_j$ does not occur in equation $i$. This is the game of Appendix D of the source; the Cleve–Mittal game on [linear constraint system games](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/linear-constraint-system-games.md) instead lets Alice answer only the variables of her equation and asks only pairs with $j \in V_i$. The region $\mathcal{C}^{(1)}_{\mathrm{EA}}$ is the union over all finite local dimensions $d$, not its closure. For the particular game of Slofstra and Vidick, the source shows that the $d$-assisted regions come arbitrarily close to $(\log m, \log n)$ as $d \to \infty$ but never contain it for finite $d$ (Propositions 5 and 6 and Corollary 7 of the source).

## Depends on

- [Multiple access channel of a nonlocal game](multiple-access-channel-of-a-nonlocal-game.md)
- [Entanglement-assisted rate region of a multiple access channel](entanglement-assisted-rate-region-of-a-multiple-access-channel.md)
- [Two-player nonlocal games: classical and entangled values](../../quantum-foundations/two-player-nonlocal-games-classical-and-entangled-values.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

A good expansion links pages for two results the proof uses: Slofstra's theorem that it is undecidable whether a linear system game has a perfect strategy in the set of finite-dimensional quantum correlations (Corollary 4 of "The set of quantum correlations is not closed", *Forum of Mathematics, Pi* 7, e1, 2019, doi:10.1017/fmp.2018.3, which is Corollary 1.4 of arXiv:1703.08618v2 and which the source cites as Corollary 1.3), and the bound on the sum rate in terms of the winning probability (Proposition 3 of the source). If a perfect finite-dimensional strategy exists, the senders draw the questions uniformly at random, answer with the perfect strategy, and always produce a winning input, so the channel reveals both questions and the pair $(\log m, \log n)$ is achieved. If none exists, the winning probability of every strategy of local dimension $d$ is below 1, and Proposition 3 keeps the sum rate of $\mathcal{C}^{(1)}_{\mathrm{EA},d}$ bounded away from $\log m + \log n$ for every finite $d$, so the pair lies outside the union. Hence the pair belongs to the region exactly when the game has a perfect finite-dimensional strategy.

## Sources

- F. Leditzky, M. A. Alhejji, J. Levin and G. Smith, "Playing games with multiple access channels", *Nature Communications* 11, article 1497, 2020, doi:[10.1038/s41467-020-15240-w](https://doi.org/10.1038/s41467-020-15240-w). Numbering of the version read, arXiv:1909.02479v2: Proposition 8 and its proof (Appendix D), the definition of linear system games at the start of Appendix D, Proposition 3 (sum rate bound), and Propositions 5 and 6 and Corollary 7 (the game of Slofstra and Vidick).
- W. Slofstra, "The set of quantum correlations is not closed", *Forum of Mathematics, Pi* 7, e1, 2019, doi:[10.1017/fmp.2018.3](https://doi.org/10.1017/fmp.2018.3); read in the open-access journal version: Corollary 4.
