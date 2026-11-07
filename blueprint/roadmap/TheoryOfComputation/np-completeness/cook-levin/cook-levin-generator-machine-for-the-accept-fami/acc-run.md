# Correctness of the accept generator, with its explicit time bound

Let $L$ be a layout
with label block size $A$ and $K$ stacks, and let $n_1, a, k_1, e, T, H$ be natural numbers with
$n_1 \le A$, $k_1 < K$ and $H > 0$. Start the accept generator for $L$, $n_1$, $a$, $k_1$, $e$ at
its start label, with internal state false, $T$ and $H$ in unary on its counters $T_n$ and $H_s$,
all other counters empty and an arbitrary bit list $o$ on its output stack. Within a number of
steps at most the explicit time bound for $L$, $n_1$, $k_1$, $T$, $H$, it reaches the label done,
with some internal state, and its output stack then holds the binary encoding of the accept family
of $L$ for $n_1$, $a$, $k_1$, $e$ at $T$, $H$ followed by $o$.

The hypotheses say that the code block fits in the label block, that $k_1$ is a stack, and that
there is a top cell.
