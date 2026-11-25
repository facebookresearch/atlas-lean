# The row-by-row check is the pairwise check

For every mode $m$ and all lists of bits
$s$ and $b$, the row-by-row check of $s$ against $b$ holds if and only if $b$ has exactly
one bit per pair $i < j < |s|$ and, listing these pairs in encoding order (rows $i$
ascending, within a row $j$ descending), the $t$-th pair $(i, j)$ and the $t$-th bit $b_t$
satisfy the pair condition $\mathrm{ok}_m(b_t, s_i, s_j)$ for every $t$.
