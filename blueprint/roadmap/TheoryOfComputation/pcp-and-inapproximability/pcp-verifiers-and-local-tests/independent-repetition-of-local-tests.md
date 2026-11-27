# Independent repetition multiplies acceptance probabilities

Let $T$ be a local test with random strings $R$ and $q$ queries. Its $k$-fold independent repetition $T^{(k)}$ has random strings $R^k$ and $kq$ queries, and passes on $(r_1, \dots, r_k)$ exactly when $T$ passes on every $r_j$. Then for every proof $\pi$,

$$\mathrm{acc}_{T^{(k)}}(\pi) = \mathrm{acc}_T(\pi)^k.$$

In particular a test with perfect completeness and soundness $1 - \varepsilon$ becomes one with perfect completeness and soundness $(1-\varepsilon)^k$ at the cost of $k$ times the queries and randomness.

## Proof sketch

The random strings are independent and uniform on $R^k$, so the probability that all $k$ coordinates pass factors as a product of $k$ equal probabilities.

## Depends on

- [Local test on a proof string](local-test-on-a-proof-string.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
