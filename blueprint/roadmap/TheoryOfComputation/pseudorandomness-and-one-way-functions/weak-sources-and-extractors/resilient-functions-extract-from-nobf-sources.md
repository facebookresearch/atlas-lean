# Resilient functions extract from non-oblivious bit-fixing sources

Let $Z$ be a distribution on $\{0,1\}^n$, $Q \subseteq [n]$ with $|Q| \le q \le n$, and suppose the marginal of $Z$ on $[n] \setminus Q$ is $t$-wise $\gamma$-biased. If $f$ is $t$-independent $(q, \varepsilon_2)$-resilient and $|\Pr_D[f = 1] - 1/2| \le \varepsilon_1$ for every $t$-wise independent $D$, then $f(Z)$ is within statistical distance $\varepsilon_1 + \varepsilon_2 + n^t\gamma$ of a uniform bit. More precisely, for any $D$ the distance of $f(Z)$ from $f(D)$ is at most $I_{Q,D}(f)$ plus the distance between the good-coordinate marginals of $Z$ and $D$. Extending a distribution on $[n]\setminus Q$ by independent uniform bits on $Q$ preserves $t$-wise independence and $t$-wise bias, which shows that $t$-independent resilience can equivalently be tested on distributions of the good coordinates.

## Proof sketch

Couple $Z$ with $D$ on the good coordinates up to their distance; where $f$ is determined by the good bits the outputs agree, and the undetermined event has probability $I_{Q,D}(f)$. Choosing $D$ $t$-wise independent within $n^t\gamma$ of the good marginal (smoothing) and using the bias bound gives the total.

## Depends on

- [Coalition influence and resilient functions](resilient-functions.md)
- [k-wise small bias is close to exact k-wise independence](../small-bias-spaces/almost-k-wise-independence-smoothing.md)

## Proof depends on

- [Maximal couplings realize statistical distance](../../../Probability/foundations/statistical-distance-and-couplings/maximal-coupling-theorem.md)

## Sources

- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics 189(3), 653–705, 2019 (numbering of ECCC TR15-119), Definitions 1.8–1.12 and Lemma 2.11 (stated there for $(t,\gamma)$-wise independent good coordinates).
- N. Alon, O. Goldreich and Y. Mansour, "Almost k-wise Independence versus k-wise Independence", Information Processing Letters 88(3), 107–110, 2003 (smoothing, which converts the $t$-wise small-bias hypothesis used here into a nearby $t$-wise independent distribution).
