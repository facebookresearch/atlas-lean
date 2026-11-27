# Alon–Yuster–Zwick: color coding for k-Path

Given a graph $G$ and a coloring $c:V(G)\to[k]$, whether $G$ has a **colorful** path on $k$ vertices (all colors distinct) is decidable in time $2^{k}\mathrm{poly}(n)$ by dynamic programming over color sets. Since a fixed $k$-vertex path is colorful under a uniformly random coloring with probability $k!/k^{k}\ge e^{-k}$, $k$-Path is solvable by a randomized algorithm in time $(2e)^{k}\mathrm{poly}(n)$. Replacing the random coloring by the colorings of a $k$-perfect family of hash functions derandomizes this to deterministic time $2^{O(k)}\mathrm{poly}(n)$, so $k$-Path is in $\mathsf{FPT}$.

## Proof sketch

For each color set $S$ and vertex $v$, record whether a colorful path with color set $S$ ends at $v$; the recurrence extends paths by one edge to a vertex of a new color. Repeating with $e^{k}$ independent random colorings finds a fixed $k$-vertex path with constant probability; a $k$-perfect hash family of size $2^{O(k)}\log n$ contains, for every $k$-set of vertices, a coloring that is injective on it.

## Depends on

- [Fixed-parameter tractable problems](../fpt.md)

## Sources

- Noga Alon, Raphael Yuster and Uri Zwick, "Color-Coding", Journal of the ACM 42(4), 1995, Lemma 3.1 and Section 4.
- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015.
