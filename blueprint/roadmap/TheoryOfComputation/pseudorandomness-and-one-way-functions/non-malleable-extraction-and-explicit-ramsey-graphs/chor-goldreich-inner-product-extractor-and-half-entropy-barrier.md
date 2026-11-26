# Inner-product extraction above half entropy and the half-entropy barrier

The inner product $\mathrm{IP}(x, y) = \sum_i x_i y_i \bmod 2$ is a two-source extractor for independent sources of min-entropies $k_1 + k_2 > n + 2\log(1/\varepsilon)$ with error $\varepsilon$; it yields explicit bipartite $K$-Ramsey graphs with $K = \sqrt{N}\cdot O(1)$ (from the Hadamard matrix). For $\mathrm{IP}$ the requirement $k_1 + k_2 > n$ cannot be dropped: for even $n$, if $X$ is uniform on a subspace $V \le \mathbb{F}_2^n$ of dimension $n/2$ and $Y$ uniform on $V^{\perp}$, then $k_1 + k_2 = n$ and $\mathrm{IP}(X, Y) = 0$ always, so for sources of equal min-entropy the inner product needs rate above $1/2$.

## Proof sketch

By Lindsey's lemma, every $S \times T$ submatrix of the $N \times N$ Hadamard matrix has entry sum at most $\sqrt{N|S||T|}$ in absolute value, which bounds the bias of $\mathrm{IP}$ on flat sources and hence on general sources (as convex combinations of flat ones).

## Depends on

- [K-Ramsey graphs and bipartite K-Ramsey graphs](ramsey-graphs-and-bipartite-ramsey-graphs.md)
- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Proof depends on

- [Two-source extractors and dispersers give Ramsey graphs](two-source-extractors-give-ramsey-graphs.md)

## Sources

- Benny Chor, Oded Goldreich, "Unbiased bits from sources of weak randomness and probabilistic communication complexity", SIAM Journal on Computing 17(2) (1988).
