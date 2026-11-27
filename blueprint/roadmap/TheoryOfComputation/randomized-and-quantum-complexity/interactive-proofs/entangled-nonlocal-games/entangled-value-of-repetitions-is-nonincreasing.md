# The entangled value of parallel repetitions is nonincreasing

For every two-prover game $G$ and $n \ge 0$, $\mathrm{val}^*(G^{n+1}) \le \mathrm{val}^*(G^{n})$ and $\mathrm{val}^*(G)^{n} \le \mathrm{val}^*(G^n)$. The first holds because restricting a strategy for $G^{n+1}$ to the first $n$ coordinates (ignoring the last check) gives a strategy for $G^n$ that wins at least as often; the second by playing independent copies of a strategy on a tensor product of states.

## Proof sketch

Restriction: questions of the extra coordinate are sampled locally with shared randomness folded into the state, and dropping a check can only increase acceptance. Tensoring independent strategies multiplies winning probabilities.

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)
- [Parallel repetition of a two-prover game](../../../pcp-and-inapproximability/two-prover-games-and-parallel-repetition/parallel-repetition-of-a-game.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
