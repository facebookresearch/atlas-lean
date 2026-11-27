# Régin's filtering algorithm for ALLDIFFERENT

Given a matching that covers the variables of an ALLDIFFERENT constraint, all values without support are found in linear time by one search from the free values and one strongly connected components computation in an oriented value graph; with Hopcroft–Karp, GAC costs $O(m\sqrt p)$ in total for $p$ variables whose domains have total size $m$.

Let $G=(X,Y,E)$ be the [value graph](alldifferent-constraint.md) of $\mathrm{ALLDIFFERENT}(X)$ with $Y$ the union of the domains, $|X|=p$, $n=|X|+|Y|$ vertices and $m=|E|=\sum_i|D_i|$ edges, given by indexed vertices and adjacency lists (the domains listed explicitly), and let $M$ be a matching covering $X$. Orient $G$ into $G_o$: every edge of $M$ from its variable to its value, every edge of $E\setminus M$ from its value to its variable. The free vertices for $M$ all lie in $Y$.

**Theorem.**

1. An edge lies on a directed cycle of $G_o$ iff it lies on an even alternating cycle of $G$, and it lies on a directed simple path of $G_o$ starting at a free vertex iff it lies on an even alternating path of $G$ starting at a free vertex.
2. An edge $e$ belongs to no matching covering $X$ iff $e\notin M$, $e$ lies on no directed path of $G_o$ starting at a free vertex, and the two endpoints of $e$ are not [strongly connected](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md) in $G_o$.
3. Hence, given $M$, the set of such edges, which by the [matching criterion](alldifferent-gac-matching-criterion.md) are exactly the values to delete for GAC, is computed in $O(m+n)$ time by a breadth-first search from the free vertices and a linear-time strongly connected components algorithm. The edges of $M$ not marked in this way are the vital edges.
4. If some domain is empty the constraint fails at once. Otherwise $p\le m$ and $|Y|\le m$, and a matching covering $X$, or the information that none exists (failure), is found by the Hopcroft–Karp algorithm in $O(\sqrt p)$ phases of $O(m)$ time each, so in $O(m\sqrt p)$ time. Hence GAC on one ALLDIFFERENT constraint is enforced from scratch in $O(m\sqrt p)$ time and $O(m)$ space, which is $O(p^{1.5}d)$ when every domain has at most $d$ values.

5. Incrementally, along one branch of search on which values are only deleted, starting from a successful propagation with covering matching $M$: after deletions, the edges of $M$ that were deleted are re-covered by augmenting paths from the current matching (at most one augmenting-path search per lost matching edge, each $O(m)$) and item 3 is rerun. Régin bounds the total cost on one constraint along such a branch by $O(m^2)$ with $m$ the initial number of edges; since $m\le pd$, this is $O(p^2d^2)$.

## Depends on

- [The ALLDIFFERENT constraint and its value graph](alldifferent-constraint.md): value graph and covering matchings.
- [Strongly connected vertices](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md): the relation used in item 2.
- [Generalized arc consistency of ALLDIFFERENT by matchings](alldifferent-gac-matching-criterion.md): unsupported values are the edges in no covering matching.

## Proof depends on

- [Edges lying in some maximum matching](edges-in-some-maximum-matching.md): Berge's characterization, applied to the covering matching $M$.
- [Hopcroft–Karp](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/maximum-bipartite-matching/hopcroft-karp.md): the matching algorithm of item 4.
- [Hopcroft and Karp's bound on the number of phases](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/maximum-bipartite-matching/card-le-hopcroft-karp-aux-sqrt.md): $O(\sqrt p)$ phases suffice when the $p$ variables form the counted side.

## Expansion

Item 1 (Régin's Proposition 1): parity is automatic for cycles because $G$ is bipartite. For paths, a directed simple path from a free vertex $y\in Y$ alternates free and matching edges; if it has odd length it ends at some $x\in X$, and since $x$ has its unique successor (its mate) not yet on the path (each value has at most one predecessor through $M$), the path extends by one matching edge to an even one.

Item 2: since $M$ covers $X$ it is a maximum matching, and covering matchings are exactly maximum matchings. By [Berge's characterization](edges-in-some-maximum-matching.md), an edge outside $M$ lies in some maximum matching iff it lies on an even alternating path from a free vertex or on an even alternating cycle, i.e. by item 1 on a directed path from a free vertex or on a directed cycle of $G_o$; an edge lies on a directed cycle iff its endpoints are in the same strongly connected component.

Items 3–4: Régin's Algorithm 2 marks the edges reached by breadth-first search from the free vertices, computes the strongly connected components with Tarjan's linear-time depth-first-search algorithm, marks the edges inside a component, and deletes the unmarked free edges, in $O(m+n)$ time; the linear bound rests on Tarjan's algorithm, not on the slower pairwise-reachability components algorithm specified in the linked strong connectivity topic. Hopcroft and Karp compute a maximum matching in $O(\sqrt s)$ phases, $s\le p$ the size of a maximum matching, each of linear cost; since every value of $Y$ lies in some domain, $|Y|\le m$ and linear cost is $O(m)$. If the matching has fewer than $p$ edges the constraint has no solution. Régin states the initialisation cost as $O(d|X_C|\sqrt{|X_C|})$.

## Sources

- J.-C. Régin, "A filtering algorithm for constraints of difference in CSPs", *Proceedings of the Twelfth National Conference on Artificial Intelligence (AAAI-94)*, AAAI Press (1994), 362–367, [https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/](https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/). Proposition 1 and its proof, Algorithm 2 (REMOVEEDGESFROMG) with its $O(m+n)$ analysis, Algorithm 3 (DIFF-PROPAGATION) and the $O(p^2d^2)$ bound, pp. 364–366.
- J. E. Hopcroft and R. M. Karp, "An $n^{5/2}$ algorithm for maximum matchings in bipartite graphs", *SIAM Journal on Computing* 2(4) (1973), 225–231, doi:10.1137/0202019. Theorem 3 (phase bound), used by Régin.
- R. Tarjan, "Depth-first search and linear graph algorithms", *SIAM Journal on Computing* 1(2) (1972), 146–160, doi:10.1137/0201010. Linear-time strongly connected components, used by Régin.
