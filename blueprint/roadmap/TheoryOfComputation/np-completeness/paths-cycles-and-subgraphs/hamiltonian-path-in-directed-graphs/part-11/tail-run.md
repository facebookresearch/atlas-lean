# The rest of a vertex step in the Hamiltonian-path verifier

Let $es$ be an edge list,
$s, t, n, c, b, a$ natural numbers and $q$ a list of natural numbers. Start the verifier, with
any flag value, at the label $\mathsf{nd}$ (the repeat scan) with its stacks in the mid-step
layout: the between-steps layout for $es$, $s$, $t$, $n$, count $c$, previous vertex $b$ and
remaining vertices $q$, with $a$ in unary on the stack $A$. Let $w$ be the unary encoding of $q$.
Then within at most $4|w| + a + b + 6$ steps it reaches the label $\mathsf{no}$ if $a \in q$ and
the label $\mathsf{loop}$ if $a \notin q$. In the second case ($a$ has been counted and become
the previous vertex) the stacks end in the between-steps layout for $es$, $s$, $t$, $n$, count
$c + 1$, previous vertex $a$ and remaining vertices $q$.
