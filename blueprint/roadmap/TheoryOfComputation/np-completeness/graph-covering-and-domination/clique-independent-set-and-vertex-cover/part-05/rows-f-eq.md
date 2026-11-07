# The CLIQUE emitter's row bits are Karp's pair bits

For every CNF formula $\varphi$, the
row bits of $\varphi$ equal the pair bits of Karp's CLIQUE graph of $\varphi$: with
$o_0, \dots, o_{m-1}$ the literal occurrences of $\varphi$, these are, for the pairs $(i, j)$ with
$i < j < m$ in encoding order (rows $i$ ascending, and $j$ descending within a row), the bits
telling whether $o_i$ and $o_j$ lie in different clauses and are not complementary.
