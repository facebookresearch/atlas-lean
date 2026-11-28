# Domino snake problems on finitely generated groups

In a snake problem a finite tileset constrains which tiles may sit at neighboring elements of a group along a self-avoiding path in its Cayley graph: one asks for a bi-infinite such path, a closed simple cycle, or a path joining two given elements.

Let $G$ be a finitely generated group with a finite generating set $S$. A *tileset graph* for $(G,S)$ is a finite multigraph $\Gamma=(A,B)$ on a set $A$ of tiles whose edges are triples $(a,a',s)$ with $s\in S\cup S^{-1}$, such that $(a',a,s^{-1})\in B$ whenever $(a,a',s)\in B$. For $I$ equal to $\mathbb Z$, $\mathbb N$ or an interval of integers, a *$\Gamma$-snake* is a pair $(\omega,\zeta)$ of an injective map $\omega:I\to G$ (the *skeleton*) and a map $\zeta:I\to A$ (the *scales*) such that, for consecutive $i,i+1\in I$, $\omega(i)^{-1}\omega(i+1)\in S\cup S^{-1}$ and $(\zeta(i),\zeta(i+1),\omega(i)^{-1}\omega(i+1))\in B$. A *$\Gamma$-ouroboros* is a pair $(\omega,\zeta)$ of maps $\omega:[0,n]\to G$ and $\zeta:[0,n]\to A$ with $n\ge3$, $\omega$ injective on $[0,n-1]$, $\omega(0)=\omega(n)$ and $\zeta(0)=\zeta(n)$, such that for all $0\le i<n$, $\omega(i)^{-1}\omega(i+1)\in S\cup S^{-1}$ and $(\zeta(i),\zeta(i+1),\omega(i)^{-1}\omega(i+1))\in B$: a correctly tiled simple non-trivial cycle with one tile at each vertex. The source writes the conditions as a snake on $[0,n]$, $n\ge2$, injective except for $\omega(0)=\omega(n)$, and means a well-tiled simple non-trivial cycle (§3); read literally, $n=2$ would admit the backtrack along one edge and its mirror edge, which every tileset graph with an edge has.

For fixed $(G,S)$, given a tileset graph $\Gamma$ (and elements $p,q\in G$):

- the *infinite snake problem* asks whether a bi-infinite $\Gamma$-snake exists;
- the *ouroboros problem* asks whether a $\Gamma$-ouroboros exists;
- the *snake reachability problem* asks whether some $\Gamma$-snake connects $p$ to $q$.

The *seeded* variants add a tile $a_0$ and require $\zeta(0)=a_0$. An instance is the finite graph $\Gamma$ (with $a_0$ for the seeded variants and, for snake reachability, $p$ and $q$ written as words over $S\cup S^{-1}$); the group $G$ and the generating set $S$ are fixed and not part of the input. Tileset graphs are effectively equivalent to Wang tiles, whose sides indexed by $S\cup S^{-1}$ carry colors, for every finitely generated group $(G,S)$; for $\mathbb Z^2$ with its standard generators these are the classical Wang tiles.

## Depends on

- [Group](../../../../GroupTheory/group-basics/group.md)
- [Cayley digraph](../../../../GraphTheory/algebraic-graph-theory/part-01/directed-cayley-graph.md)

## Proof depends on

None.

## Expansion

For $\mathbb Z^2$ with generators $(1,0),(0,1)$, snake reachability is PSPACE-complete (Etzion-Petruschka, Harel and Myers, *Theoretical Computer Science* 131, 1994), the infinite snake problem is $\Pi^0_1$-complete (Adleman, Kari, Kari and Reishus) and the ouroboros problem is $\Sigma^0_1$-complete (Ebbinghaus; Kari), as the source recalls. On virtually free groups all three problems and their seeded versions are decidable for every generating set, since they are expressible in monadic second-order logic over the Cayley graph.

## Sources

- Nathalie Aubrun and Nicolas Bitar, "Domino Snake Problems on Groups", in *Fundamentals of Computation Theory (FCT 2023)*, Lecture Notes in Computer Science 14292, Springer, 2023, pp. 46–59, doi:[10.1007/978-3-031-43587-4_4](https://doi.org/10.1007/978-3-031-43587-4_4); read in arXiv:2307.12655v1 ([arXiv](https://arxiv.org/abs/2307.12655v1)), whose numbering is used: Section 3 (Definitions 3 to 5: tileset graphs, snakes, ouroboros, the three problems and their seeded variants; Theorem 1 recalling the results for $\mathbb Z^2$), Section 7 (Theorem 5 and Corollary 3: monadic second-order logic and virtually free groups) and Appendix B (Lemmas 4 and 5: equivalence of Wang tiles and tileset graphs).
