# The characteristic vector of a good vertex set is accepted

Let $m$ be a mode, $k$ and
$n$ natural numbers, let $\mathit{bits}$ be a bit list with one bit per pair $(i, j)$,
$i < j < n$, and let $s$ be a set of $k$ vertices of $\{0, \dots, n - 1\}$ that meets the pair
condition of $m$ on every pair $i < j$. Then the verifier for mode $m$ accepts the encoding of
$(k, n, \mathit{bits})$ with witness the characteristic vector of $s$: the list of $n$ bits whose
$i$-th bit is set if and only if $i \in s$.
