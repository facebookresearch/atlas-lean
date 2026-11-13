# Karp's CLIQUE instance of a CNF formula

For a CNF formula $\varphi$ with $m$ clauses and
$N$ literal occurrences, the bit string encoding the instance $(m, G)$: $m$ ones, a zero, $N$
ones, a zero, then one adjacency bit for each pair $(i, j)$ with $i < j < N$, listed by $i$
ascending and, for each $i$, by $j$ descending, a true bit meaning that $i$ and $j$ are adjacent.
The graph $G$ has the literal occurrences of $\varphi$, in order, as its vertices
$0, \dots, N - 1$, and two occurrences are adjacent when they lie in different clauses and are
not complementary (the same variable with opposite polarities).
