# Well-formed succinct circuit descriptions

Let $C$ be a list of encoded gates, read as a
flat Boolean circuit on $n$ inputs that describes a circuit $D$ with $2^n$ gates. For each gate
$i$ of $D$, let $t_i$, $p_i$ and $q_i$ be its gate type, first predecessor and second
predecessor, as decoded from the outputs of $C$ on the $n$-bit binary expansion of $i$. The
description is well formed when, for every $i < 2^n$: if $i < n$, then $t_i = 0$ (gate $i$ is an
input gate); and if $i \ge n$, then either $t_i = 4$ or $t_i = 5$ (a constant gate), or
$p_i < i$ and $q_i < i$.
