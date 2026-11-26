# Rejection gaps of anchored games scale by (1 − α)²

For every finite game $G$ with nonempty answer sets and every $\alpha \in [0,1]$,

$$1 - \mathrm{val}(G_\perp) = (1 - \alpha)^2 \big(1 - \mathrm{val}(G)\big), \qquad 1 - \mathrm{val}^*(G_\perp) = (1 - \alpha)^2 \big(1 - \mathrm{val}^*(G)\big).$$

In particular $G_\perp$ has value $1$ iff $G$ does, classically and in the entangled setting.

## Proof sketch

The game is lost only when neither question is anchored, an event of probability $(1-\alpha)^2$ independent of the questions; on that event the players face exactly $G$. Strategies for $G_\perp$ restrict to strategies for $G$ and every strategy for $G$ extends by arbitrary answers to $\perp$, preserving local dimensions.

## Depends on

- [Anchoring a two-prover game](anchoring-a-two-prover-game.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
