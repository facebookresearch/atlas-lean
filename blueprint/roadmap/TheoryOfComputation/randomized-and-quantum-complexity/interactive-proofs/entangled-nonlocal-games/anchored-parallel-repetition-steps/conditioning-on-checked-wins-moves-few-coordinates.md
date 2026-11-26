# Conditioning anchored repetitions on checked wins moves few coordinates

Fix a finite-dimensional tensor strategy with local POVMs for the $n$-fold repetition of an $\alpha$-anchored game, a set $C$ of checked coordinates, and the event $W$ that every checked coordinate is won, with $\Pr[W] > 0$. Let $\varepsilon_1 = \frac{1}{n - |C|}\big(\ln \frac{1}{\Pr[W]} + |C| \ln|\mathcal{Z}|\big)$, where $\mathcal{Z}$ is the full checked-answer alphabet, and let $\varepsilon_2$ be the analogous quantity for the transcript. Then, summed over the free coordinates $j \notin C$ and normalized, (1) the squared half-$L_1$ distances between the free trial distributions conditioned on $W$ and unconditioned are $O(\varepsilon_1)$; (2) the transcript and question-resampling distances are $O(\varepsilon_1 + \varepsilon_2)$; and (3) with the weight $w = \alpha^2/2$ coming from the two-anchor events, comparisons of anchored transcripts satisfy the bounds $(2 + 2w)\varepsilon_1 + \varepsilon_2$ and $(1 + w)(2 \varepsilon_1 + \varepsilon_2)$.

## Proof sketch

Conditioning a product law on an event of probability $p$ costs total KL divergence $\ln(1/p)$ plus the entropy of the conditioned answers; chain-rule this over the free coordinates and apply Pinsker with constant $1/2$. The anchor events contribute an extra weight $w$ because transcripts with both questions anchored are independent of the strategy.

## Depends on

- [Anchoring a two-prover game](anchoring-a-two-prover-game.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)

## Proof depends on

- [Conditional independence of the noisy reveal in anchored repetition](noisy-reveal-conditional-independence.md)
- [Holenstein's embedding lemma for conditioned repetitions](../../../../pcp-and-inapproximability/two-prover-games-and-parallel-repetition/holenstein-embedding-lemma.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
