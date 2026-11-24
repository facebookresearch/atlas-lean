# Polynomial time bound of the accept generator

Let $L$ be a layout with label block size
$A$, $K$ stacks and $g$ symbol codes, let $n_1, a, k_1, e, T, H$ be natural numbers with
$n_1 \le A$, $k_1 < K$ and $H > 0$, and let $c = 314\,(A + K + g + n_1 + k_1 + 1)^5$. Start the
accept generator for $L$, $n_1$, $a$, $k_1$, $e$ at its start label, with internal state false,
$T$ and $H$ in unary on its counters $T_n$ and $H_s$, all other counters empty and an arbitrary
bit list $o$ on its output stack. Within at most $c\,(T + H + 1)^4$ steps it reaches the label
done, with some internal state, and its output stack then holds the binary encoding of the accept
family of $L$ for $n_1$, $a$, $k_1$, $e$ at $T$, $H$ followed by $o$.
