# The 0-1 permanent counts perfect matchings

Let $B$ be a relation on a finite set $n$, read as a bipartite graph between rows and columns ($B(i,j)$:
row $i$ is adjacent to column $j$), and let $A$ be its 0-1 biadjacency matrix over a commutative
semiring. Then

$$\operatorname{per} A = \#\{\sigma \in \operatorname{Sym}(n) : B(\sigma(j), j) \text{ for every column } j\},$$

the number of perfect matchings of the bipartite graph. This is the correspondence Valiant uses to
read the $\#P$-completeness of the 0-1 permanent as the $\#P$-completeness of counting perfect
matchings in bipartite graphs, a problem whose decision version is solvable in polynomial time.

## Sources

- L. G. Valiant, *The complexity of computing the permanent*, Theoretical Computer Science 8 (1979), 189-201, Section 1.
