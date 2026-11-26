# Conditioning anchored repetitions on checked wins moves few coordinates

Fix a finite-dimensional tensor strategy with local POVMs for the $n$-fold repetition of an $\alpha$-anchored game, a set $C$ of checked coordinates, and the event $W$ that every checked coordinate is won, with $\Pr[W] > 0$. Let $\varepsilon_1 = \frac{1}{n - |C|}\big(\ln \frac{1}{\Pr[W]} + |C| \ln|\mathcal{Z}|\big)$, where $\mathcal{Z}$ is the full checked-answer alphabet. Then the sum over the free coordinates $j \notin C$ of the squared half-$L_1$ distances between the free trial distributions conditioned on $W$ and unconditioned, divided by $n - |C|$, is $O(\varepsilon_1)$.

## Proof sketch

Conditioning a product law on an event of probability $p$ costs total KL divergence $\ln(1/p)$ plus the entropy of the conditioned answers; chain-rule this over the free coordinates and apply Pinsker with constant $1/2$.

## Depends on

- [Anchoring a two-prover game](anchoring-a-two-prover-game.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
