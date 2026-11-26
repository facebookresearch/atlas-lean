# Cover complexity of the inequality graph and of random bipartite graphs

For bipartite graphs on vertex sets $\{0,1\}^n\times\{0,1\}^n$ viewed as sets of pairs, with supplied sets the rows and columns given by literals: (i) the inequality graph $\{(u,v):u\neq v\}$ has cover complexity exactly $n$; (ii) every graph with $N$ vertices per side has a pair cover of length $N$, but for $N\ge16$ a uniformly random such graph has no cover of length at most $N/16$ except with probability at most $2^{-N}$. Since graph covers transfer to Boolean literal covers of the same length, this yields linear lower bounds on fusion cover complexity for random bipartite-graph functions.

## Proof sketch

(i) The canonical semifilter at $(u,v)$ accepts sets containing $(u,u)$ or $(v,v)$; any defeating pair separates the diagonal points by membership in its first component, so a cover injectively labels the $2^n$ vertices by its length in bits. (ii) A cover of length $k$ is determined by a description of $O(k(N+k))$ inclusion-flag bits, while there are $2^{N^2}$ graphs.

## Depends on

- [Semifilters and semifilter (fusion) covers](semifilters-and-fusion-covers.md)

## Sources

- Bruno P. Cavalar, Igor C. Oliveira, "Boolean Circuit Complexity and Two-Dimensional Cover Problems", Electronic Colloquium on Computational Complexity, 2025.
