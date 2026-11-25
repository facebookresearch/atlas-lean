# Run of the load phase

Let $m$ be a mode, $n$ and $j$ natural numbers and $w$ and
$\mathit{acc}$ bit lists. Start the verifier for mode $m$ at the load label, in any internal
state, with $n$ in unary on the counter $N$, $j$ in unary on the counter $C$, $w$ on the witness
stack $W$ and $\mathit{acc}$ on the vertex stack $V$. Then within at most $n + 1$ steps the
machine reaches the walk label with its flag $c$ (the conjunction of the row's pair conditions
so far) set to true if $w$ has at least $n$ bits and exactly $j$ of its first $n$ bits are set,
and the reject label otherwise. In the first case $V$ then holds the first $n$ bits of $w$, bit
$n - 1$ on top, above $\mathit{acc}$, and the stacks $X$ and $T$ are unchanged.
