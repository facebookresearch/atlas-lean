# Inner-product extraction above half entropy and the half-entropy barrier

The inner product $\mathrm{IP}(x, y) = \sum_i x_i y_i \bmod 2$ is a two-source extractor for independent sources of min-entropies $k_1 + k_2 > n + 2\log(1/\varepsilon)$ with error $\varepsilon$; it yields explicit bipartite $K$-Ramsey graphs with $K = \sqrt{N}\cdot O(1)$ (from the Hadamard matrix). For decades explicit constructions remained near the barrier $K = N^{\Theta(1)}$, far from the existential $K = O(\log N)$, until Bourgain's $0.499n$ extractor and the line of work culminating in logarithmic entropy.

## Proof sketch

By Lindsey's lemma, every $S \times T$ submatrix of the $N \times N$ Hadamard matrix has entry sum at most $\sqrt{N|S||T|}$ in absolute value, which bounds the bias of $\mathrm{IP}$ on flat sources and hence on general sources (as convex combinations of flat ones).

## Depends on

- [Two-source extractors and dispersers give Ramsey graphs](two-source-extractors-give-ramsey-graphs.md)

## Proof depends on

- [Two-source extractors and dispersers give Ramsey graphs](two-source-extractors-give-ramsey-graphs.md)

## Sources

- Benny Chor, Oded Goldreich, "Unbiased bits from sources of weak randomness and probabilistic communication complexity", SIAM Journal on Computing 17(2) (1988).
