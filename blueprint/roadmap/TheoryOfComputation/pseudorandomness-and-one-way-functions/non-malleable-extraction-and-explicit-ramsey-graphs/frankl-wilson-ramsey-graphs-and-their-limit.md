# Frankl-Wilson explicit Ramsey graphs

For a prime $p$, the graph on $\binom{[p^3]}{p^2 - 1}$ in which two sets are adjacent iff their intersection size is $\equiv -1 \pmod p$ is $K$-Ramsey with $K = \binom{p^3}{p-1}$. In terms of the number of vertices $N$, this gives explicit $K$-Ramsey graphs with $K = 2^{O(\sqrt{\log N \log\log N})}$.

## Proof sketch

An independent set, respectively a clique, is a family of sets with intersection sizes avoiding, respectively lying in, the residue class $-1 \bmod p$. The Frankl-Wilson modular intersection theorem, proved by the linear-algebra (polynomial) method on characteristic vectors, bounds both families by $\binom{p^3}{p-1}$.

## Depends on

- [K-Ramsey graphs and bipartite K-Ramsey graphs](ramsey-graphs-and-bipartite-ramsey-graphs.md)

## Sources

- Peter Frankl, Richard M. Wilson, "Intersection theorems with geometric consequences", Combinatorica 1(4) (1981).
