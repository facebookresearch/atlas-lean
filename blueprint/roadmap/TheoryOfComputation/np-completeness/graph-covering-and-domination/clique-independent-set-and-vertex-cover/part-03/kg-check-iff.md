# Characterization of the CLIQUE verifier

For a mode $m$ and bit lists $x$ and $w$, the
verifier for mode $m$ accepts input $x$ with witness $w$ if and only if there are $k$, $n$ and a
bit list $\mathit{bits}$ such that $x$ is the encoding of the instance $(k, n, \mathit{bits})$,
$\mathit{bits}$ has one bit per pair $(i, j)$ with $i < j < n$, $w$ has at least $n$ bits,
exactly $k$ of the first $n$ bits of $w$ are set, and for all $i < j < n$ the pair condition of
$m$ holds for the bit of the pair $\{i, j\}$ and the bits $w_i$ and $w_j$.
