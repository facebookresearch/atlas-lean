# Achieving the ideal rate pair with entanglement is undecidable for game channels

No algorithm decides, given a linear system over $\mathbb{F}_2$, whether senders sharing finite-dimensional entanglement can reach the ideal rate pair $(\log m, \log n)$ on the multiple access channel built from the system's nonlocal game.

**Theorem (Leditzky, Alhejji, Levin and Smith).** Let $Ax = b$ be an $m \times n$ linear system over $\mathbb{F}_2$, let $G_{\mathrm{LS}}$ be its [linear system game](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/linear-constraint-system-games.md), and let $N_{G_{\mathrm{LS}}}$ be the [multiple access channel of the game](multiple-access-channel-of-a-nonlocal-game.md). It is undecidable to determine whether the rate pair $(\log m, \log n)$ belongs to the entanglement-assisted achievable rate region $\mathcal{C}^{(1)}_{\mathrm{EA}}(N_{G_{\mathrm{LS}}})$.

In the linear system game, Alice receives an equation $i \in [m]$ and answers with an assignment $y \in \mathbb{F}_2^n$ that satisfies equation $i$. Bob receives a variable $j \in [n]$ and answers with a bit. They win if $x_j$ does not occur in equation $i$ or if Bob's bit equals $y_j$. The region $\mathcal{C}^{(1)}_{\mathrm{EA}}$ is the union over all finite local dimensions $d$. For the particular game of Slofstra and Vidick, the source shows that the $d$-assisted regions come arbitrarily close to $(\log m, \log n)$ as $d \to \infty$ but never contain it for finite $d$.

## Depends on

- [Multiple access channel of a nonlocal game and its entanglement-assisted rate region](multiple-access-channel-of-a-nonlocal-game.md)
- [Linear constraint system games and operator solutions](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/linear-constraint-system-games.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from a theorem of Slofstra (Corollary 1.3 of "The set of quantum correlations is not closed", *Forum of Mathematics, Pi* 7, e1, 2019, doi:10.1017/fmp.2018.3, as quoted in the source): it is undecidable whether a linear system game has a perfect strategy in the set of finite-dimensional quantum correlations. If such a strategy exists, the senders draw the questions uniformly at random, answer with the perfect strategy, and always produce a winning input, so the channel reveals both questions and the pair $(\log m, \log n)$ is achieved. If no perfect finite-dimensional strategy exists, the winning probability of every strategy of local dimension $d$ is below 1. A bound on the sum rate in terms of the winning probability (Proposition 3 of the source) then keeps the sum rate of $\mathcal{C}^{(1)}_{\mathrm{EA},d}$ bounded away from $\log m + \log n$ for every finite $d$, so the pair lies outside the union. Hence the pair belongs to the region exactly when the game has a perfect finite-dimensional strategy.

## Sources

- F. Leditzky, M. A. Alhejji, J. Levin and G. Smith, "Playing games with multiple access channels", *Nature Communications* 11, article 1497, 2020, doi:[10.1038/s41467-020-15240-w](https://doi.org/10.1038/s41467-020-15240-w). Numbering of the version read, arXiv:1909.02479v2: Proposition 8 and its proof (Appendix D), the definition of linear system games at the start of Appendix D, Proposition 3 (sum rate bound), and Propositions 5 and 6 and Corollary 7 (the game of Slofstra and Vidick).
