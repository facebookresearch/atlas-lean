# One vertex step of the Hamiltonian-path verifier

Let $es$ be an edge list,
$s, t, n, c, b, a$ natural numbers and $q$ a list of natural numbers. Start the verifier, with
any flag value, at the label $\mathsf{rdA}$ (read the next vertex) with its stacks in the
between-steps layout for $es$, $s$, $t$, $n$, count $c$, previous vertex $b$ and remaining
vertices $a, q$. Let $e$ be the bit encoding of $es$ and $w$ the unary encoding of $q$. Then
within at most $8a + b + 4|e| + 4|w| + 20$ steps it reaches the label $\mathsf{loop}$ if the
step check on $a$ passes and the label $\mathsf{no}$ otherwise. The step check passes when
$a < n$, $a = s$ in case $c = 0$ and $(b, a) \in es$ in case $c \ne 0$, and $a \notin q$. When
it passes, the stacks end in the between-steps layout for $es$, $s$, $t$, $n$, count $c + 1$,
previous vertex $a$ and remaining vertices $q$.
