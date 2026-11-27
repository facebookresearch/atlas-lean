# Buss's kernel for vertex cover

Given a graph $G$ and an integer $k$, repeatedly put every vertex of degree greater than $k$ into the cover, decreasing $k$ by one each time, and delete isolated vertices. If the reduced graph has more than $k'^2$ edges, where $k'$ is the remaining budget, then $G$ has no vertex cover of size at most $k$. Otherwise the reduced instance has at most $k'^2$ edges and $2k'^2$ vertices, and it has a vertex cover of size at most $k'$ if and only if $G$ has one of size at most $k$.

## Expansion

This page becomes ready once these prerequisites are stated:

- Executable graph representations and size measures (proof prerequisite; not yet stated)
- The statement must be checked against the cited sources, which have not been opened

## Sources

- J. F. Buss and J. Goldsmith, "Nondeterminism within P", *SIAM Journal on Computing* 22(3):560–572, 1993
- M. Cygan et al., *Parameterized Algorithms*, Springer, 2015
