# Conditional independence of the noisy reveal in anchored repetition

In the dependency-breaking step for repetitions of an $\alpha$-anchored game, a coordinate's question pair $(x, y)$ is accompanied by a public *noisy message* which reveals Alice's question, Bob's question, or an anchor symbol, according to fixed rates. For every joint question law, the joint law of $(x, y)$ and the message factors as the message mass times two local conditional laws, so $x$ and $y$ are conditionally independent given every supported message. For either designated player, forgetting the message recovers the anchored question law exactly (for all $\alpha \in [0,1]$), and for interior rates the left-message conditional agrees with the original anchored conditional at supported messages.

## Proof sketch

Write the noisy-message channel explicitly: given a message revealing one side, the other side is drawn from the conditional of $\mu$, and anchors are chosen independently; summing out the message telescopes back to the anchored marginal.

## Depends on

- [Anchoring a two-prover game](anchoring-a-two-prover-game.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
