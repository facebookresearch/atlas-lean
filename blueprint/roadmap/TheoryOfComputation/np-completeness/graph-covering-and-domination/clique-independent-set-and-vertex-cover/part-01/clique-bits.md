# Adjacency bits of Karp's clique graph

For a CNF formula $\varphi$, list its literal
occurrences $o_0, \dots, o_{m-1}$ in formula order, each recorded by its clause index, its
variable and its polarity. The result has one bit for each pair $(i, j)$ with $i < j < m$, the
pairs taken in encoding order ($i$ ascending and, for each $i$, $j$ descending). The bit of
$(i, j)$ is true exactly when $o_i$ and $o_j$ lie in different clauses and are not
complementary, that is, are not occurrences of the same variable with opposite polarities.
