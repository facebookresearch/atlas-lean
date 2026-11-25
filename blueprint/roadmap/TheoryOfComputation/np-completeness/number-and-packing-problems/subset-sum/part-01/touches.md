# Pairs touching a vertex

Let $p_0, \dots, p_{m-1}$ be the vertex pairs $(i, j)$ with
$i < j < n$ in encoding order (rows $i$ ascending, within a row $j$ descending). For a list $b$
of pair bits, a vertex $v$ and an index $q$, the test is true when bit $b_q$ is set and $v$ is one
of the two entries of $p_q$. An index past the end of $b$ counts as an unset bit, and for
$q \ge m$ the pair $p_q$ is taken to be $(0, 0)$.
