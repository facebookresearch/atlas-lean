# Conditioning anchored repetitions on checked wins moves few coordinates

Fix an $\alpha$-anchored game with $0 < \alpha < 1$, answer sets $\mathcal{A}$ and $\mathcal{B}$ and predicate $V$, a number $n \ge 1$ of repetitions and a finite-dimensional tensor strategy with local POVMs for the $n$-fold repetition. Draw $n$ independent copies $(D_j, M_j, X_j, Y_j)$ of the noisy-reveal variables of the linked page with $\eta = \alpha/2$, and answers $(\mathbf{A}, \mathbf{B})$ that, given the questions $(\mathbf{X}, \mathbf{Y})$, are independent of $(\mathbf{D}, \mathbf{M})$ and follow the Born rule of the strategy, so that $(\mathbf{X}, \mathbf{Y}, \mathbf{A}, \mathbf{B})$ is distributed as in the repeated game. Fix a set $C$ of checked coordinates and the event $W$ that $V(X_j, Y_j, A_j, B_j) = 1$ for every $j \in C$, with $\Pr[W] > 0$. The *free trial* of a coordinate $j \notin C$ is the tuple $(D_j, M_j, X_j, Y_j)$, and $\mathcal{Z} = \mathcal{A} \times \mathcal{B}$ is the *full checked-answer alphabet*, the set of answer pairs of one checked coordinate. Let $\varepsilon_1 = \frac{1}{n - |C|}\big(\ln \frac{1}{\Pr[W]} + |C| \ln|\mathcal{Z}|\big)$. Then the sum over the free coordinates $j \notin C$ of the squared half-$L_1$ distances between the law of the free trial of $j$ conditioned on $W$ and its unconditioned law, divided by $n - |C|$, is $O(\varepsilon_1)$ (Bavarian, Vidick and Yuen, Section 4.3, Lemma 4.6, item 1 and its proof, with $\Omega_j = (D_j, M_j)$ and $\delta$ of their eq. (4)).

## Proof sketch

The free trials of distinct coordinates are independent. Conditioning their joint law on $W$ costs KL divergence at most $\ln(1/\Pr[W])$ from that product law, and against a product law this divergence is at least the sum of the coordinatewise divergences (Holenstein's Lemma 4.1, quoted by Bavarian, Vidick and Yuen as their Lemma 4.7). Pinsker's inequality with constant $1/2$ turns each divergence into a squared half-$L_1$ distance, so the sum is at most $\tfrac12 \ln(1/\Pr[W]) \le \tfrac12 (n - |C|)\,\varepsilon_1$.

## Depends on

- [Anchoring a two-prover game](anchoring-a-two-prover-game.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)
- [Conditional independence of the noisy reveal in anchored repetition](noisy-reveal-conditional-independence.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
