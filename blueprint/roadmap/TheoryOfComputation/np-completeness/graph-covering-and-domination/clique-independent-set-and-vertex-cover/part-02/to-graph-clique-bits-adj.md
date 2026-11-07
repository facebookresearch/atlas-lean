# Adjacency in Karp's clique graph

Let $\varphi$ be a CNF formula and let
$o_0, \dots, o_{m-1}$ be its literal occurrences (clause index, variable, polarity) in formula
order. In Karp's graph of $\varphi$, the graph on $\{0, \dots, m-1\}$ read off the clique pair
bits of $\varphi$, vertices $i$ and $j$ are adjacent if and only if $i \ne j$ and the occurrences
$o_i$ and $o_j$ are adjacent, that is, they lie in different clauses and are not complementary
(they are not the same variable with opposite polarities).
