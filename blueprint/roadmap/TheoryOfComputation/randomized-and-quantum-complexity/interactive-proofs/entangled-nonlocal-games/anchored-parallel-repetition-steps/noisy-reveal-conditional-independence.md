# Conditional independence of the noisy reveal in anchored repetition

Let $\mu$ be the question law of an $\alpha$-anchored game with $0 < \alpha < 1$, and let $0 \le \eta \le \alpha$ (Bavarian, Vidick and Yuen take $\eta = \alpha/2$). Draw $D$ uniformly from $\{A, B\}$. If $D = A$, let $M$ take each question $x \ne \perp$ of Alice with probability $\mu_X(x)/(1 - \eta)$ and the value $\perp$ with probability $(\alpha - \eta)/(1 - \eta)$, let $X = M$ with probability $1 - \eta$ and $X = \perp$ otherwise, and draw $Y$ from $\mu_{Y \mid X}(\cdot \mid M)$; if $D = B$, do the same with the players exchanged. Then $X$ and $Y$ are independent given $(D, M)$, and for each $d \in \{A, B\}$ the law of $(X, Y)$ given $D = d$ is $\mu$ (Bavarian, Vidick and Yuen, Section 4.1, Claims 4.1 and 4.2).

## Proof sketch

Given $(D, M) = (A, m)$, $X$ is a function of $m$ and independent noise, while $Y$ is drawn from a law that depends only on $m$, which gives the conditional independence. Summing over $M$ given $D = A$, $X = x \ne \perp$ has probability $(1 - \eta)\mu_X(x)/(1 - \eta) = \mu_X(x)$ and $X = \perp$ has probability $\alpha$, and since $\mu_{XY}(\perp, y) = \alpha\,\mu_Y(y)$ in an anchored game, $Y$ given $X$ has law $\mu_{Y \mid X}$; the case $D = B$ is symmetric.

## Depends on

- [Anchoring a two-prover game](anchoring-a-two-prover-game.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
