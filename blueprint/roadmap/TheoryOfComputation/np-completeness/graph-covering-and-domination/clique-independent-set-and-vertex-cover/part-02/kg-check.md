# The verifier for CLIQUE, INDEPENDENT-SET and VERTEX-COVER

For a mode $m$, an input
$x$ and a witness $w$ (bit lists), the verifier rejects if $x$ does not decode to a triple
$(k, n, \mathit{bits})$. Otherwise it accepts if and only if $\mathit{bits}$ has one bit per
pair $(i, j)$ with $i < j < n$, $w$ has at least $n$ bits, exactly $k$ of the first $n$ bits of
$w$ are set, and for every pair $(i, j)$, matched with its bit $b$ in the encoding order of the
pairs, the pair condition of $m$ holds for $b$, $w_i$ and $w_j$. So the first $n$ bits of $w$
choose the vertices.
