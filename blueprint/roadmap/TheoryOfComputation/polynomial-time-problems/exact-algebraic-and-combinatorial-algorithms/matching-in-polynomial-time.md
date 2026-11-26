# Bipartite perfect matching and maximum matching in polynomial time

Deciding whether a bipartite graph has a perfect matching, and computing a maximum matching in a general graph (Edmonds' blossom algorithm), are possible in polynomial time on multi-tape Turing machines; the parity of the number of perfect matchings of a bipartite graph equals the determinant of its biadjacency matrix modulo $2$ and is also polynomial-time computable.

## Proof sketch

Augmenting paths: a matching is maximum iff no augmenting path exists (Berge); search for one by alternating BFS, contracting odd cycles (blossoms) in non-bipartite graphs. The parity statement follows from $\operatorname{perm}\equiv\det\pmod 2$.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)
- [The 0-1 permanent counts perfect matchings](../../counting-complexity/complexity-of-the-permanent/permanent-boole-eq-card.md)

## Proof depends on

- [Permanent equals determinant in characteristic two](../../counting-complexity/complexity-of-the-permanent/permanent-eq-det-of-char-p-two.md)

## Sources

- Jack Edmonds, "Maximum Matching and a Polyhedron with 0,1-Vertices", Journal of Research of the National Bureau of Standards, Section B 69B(1–2), 1965.
- John E. Hopcroft and Richard M. Karp, "An n^5/2 Algorithm for Maximum Matchings in Bipartite Graphs", SIAM Journal on Computing 2(4), 1973.
