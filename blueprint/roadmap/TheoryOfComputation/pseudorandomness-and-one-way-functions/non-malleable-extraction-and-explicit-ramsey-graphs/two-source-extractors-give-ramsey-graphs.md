# Two-source extractors and dispersers give Ramsey graphs

Let $f : \{0,1\}^n \times \{0,1\}^n \to \{0,1\}$ be such that for all independent random variables $X, Y$ uniform on subsets of size $2^k$, $f(X, Y)$ takes both values with positive probability (a *two-source disperser* for min-entropy $k$; any two-source extractor with error $< 1/2$ qualifies). Then the bipartite graph on $\{0,1\}^n \times \{0,1\}^n$ with edges $\{(x, y) : f(x, y) = 1\}$ is bipartite $2^k$-Ramsey with $N = 2^n$. If $f$ is moreover symmetric, the graph on $\{0,1\}^n$ with $x \sim y$ iff $f(x,y) = 1$ ($x \ne y$) is $2^{k+1}$-Ramsey.

## Proof sketch

A complete or empty bipartite subgraph on $S \times T$ with $|S| = |T| = 2^k$ means $f$ is constant on $S \times T$, i.e. constant on the flat sources uniform on $S$ and $T$. For the non-bipartite case, a clique or independent set $Q$ of size $2^{k+1}$ splits into two disjoint halves $S, T$ on which $f$ is constant.

## Depends on

- [K-Ramsey graphs and bipartite K-Ramsey graphs](ramsey-graphs-and-bipartite-ramsey-graphs.md)
- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Sources

- Eshan Chattopadhyay, David Zuckerman, "Explicit two-source extractors and resilient functions", Annals of Mathematics 189(3) (2019), STOC (2016); ECCC TR15-119.
- Boaz Barak, Anup Rao, Ronen Shaltiel, Avi Wigderson, "2-source dispersers for n^{o(1)} entropy, and Ramsey graphs beating the Frankl-Wilson construction", Annals of Mathematics 176(3) (2012).
