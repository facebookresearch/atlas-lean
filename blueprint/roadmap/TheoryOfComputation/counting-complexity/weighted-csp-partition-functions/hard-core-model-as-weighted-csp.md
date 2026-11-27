# The hard-core model as a weighted CSP

For a graph $G$ on vertices $\{0,\dots,n-1\}$ with edge list $E$ and fugacity $\lambda$, the instance with a unary constraint on each vertex weighted $\lambda$ when its variable is true and $1$ otherwise, and a binary constraint on each edge weighted $0$ when both endpoints are true and $1$ otherwise, has partition function $Z = \sum_{I} \lambda^{|I|}$, the sum over all independent sets $I$ of $G$ (the independence polynomial evaluated at $\lambda$).

## Proof sketch

An assignment is the indicator of a vertex set; edge weights vanish unless the set is independent, and vertex weights contribute $\lambda^{|I|}$.

## Depends on

- [Partition function of a weighted CSP](partition-function-of-a-weighted-csp.md)

## Sources

- Dror Weitz, "Counting Independent Sets up to the Tree Threshold", Proceedings of the 38th Annual ACM Symposium on Theory of Computing (STOC 2006), 2006 (the hard-core model and its partition function).
- N. Alon and J. H. Spencer, The Probabilistic Method, 4th ed., Wiley, 2016.
