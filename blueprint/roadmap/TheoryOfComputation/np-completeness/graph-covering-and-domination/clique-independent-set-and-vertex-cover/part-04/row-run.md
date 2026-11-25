# One row of the clique verifier's walk

Let $m$ be a mode, $s_i$ a bit, $r$ and $b$
lists of bits, $v$ a state and $S$ stack contents in which the vertex stack $V$ holds, from
the top, the bits of the reverse $\rho$ of $r$ followed by $s_i$, the scratch stack $T$ is
empty, and the input stack $X$ holds the bits $b$. Call the row condition: $|r| \le |b|$,
and either $s_i$ is free for $m$ or $\mathrm{sat}_m(b_t, \rho_t)$ holds for every $t < |r|$
(indices from $0$). Then there are a state $v'$ and stack contents $S'$ such that within at
most $2|r| + 2$ steps the verifier program of mode $m$ goes from label walk(true) with
state $v$ and stacks $S$ to state $v'$ and stacks $S'$ at label walk(true) if the row
condition holds and at the rejecting label otherwise; and if the row condition holds, then
in $S'$ the stack $V$ holds the bits of $\rho$, $T$ is empty, and $X$ holds $b$ with its
first $|r|$ bits dropped.
