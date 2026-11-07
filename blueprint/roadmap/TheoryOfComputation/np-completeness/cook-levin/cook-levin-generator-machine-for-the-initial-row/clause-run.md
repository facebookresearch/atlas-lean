# Run of one clause (initial-row generator)

Let $L$ be a layout with $g$ symbol codes, let
$i_c$ and $k_0$ be natural numbers and let $y$ be a list of $n$ certificate codes. Let $c$ be a
clause kind for $g$ and $n$ that is well formed for $i_c$, $g$ and $y$, and let $V, B$ be natural
numbers such that all literals of $c$ at base $B$ (for $i_c$, $g$ and $y$) are in range below $V$.
Let $F$ be counter values of the generator with empty scratch counters such that $F(b) = B$ for
the base counter $b$ of $c$, $F(\mathrm{Vc}) = V$ and $F(P) = 0$. Then for every output $o$ and
flag $v$, the counter part of the generator for $L$, $i_c$, $k_0$, $y$ runs within the step bound
$\mathrm{clauseB}(n + 2, V)$ for one clause from the clause-start label of $c$, with flag $v$,
counters $F$ and output $o$, to the label after $c$, with flag false, counters $F$ and output
$w \cdot o$, where $w$ is the dense encoding of the dense clause over $V$ variables built from the
literal list of $c$ at base $B$ (for $i_c$, $g$ and $y$).
