# Run of the accept cell chain

Let $L$ be a layout with $g$ symbol codes, let
$n_1, a_c, k_1, e_a \in \mathbb{N}$ be the parameters of the generator, and let $F$ give a value
to every counter of the generator such that the scratch counters $\mathsf{Q}$, $\mathsf{tmp}$,
$\mathsf{md}$, $\mathsf{c1}$, $\mathsf{c2}$ are $0$, $F(\mathsf{Vc}) = V$, $F(\mathsf{P}) = 0$,
$F(\mathsf{TW}) + n_1 \le V$ and $F(\mathsf{CB}) + g \le V$. Write
$B(V) = V(3V + 6) + 10V + 13$ for the one-clause step bound. Then for every $x < g$, every
output stack $o$ and every state bit $v$, the generator started at the entry label of cell
clause $x$ with state $v$, counters $F$ and output $o$ reaches the halting label $\mathrm{done}$
within $(x + 1)B(V) + n_1 B(V)$ steps, with state false, counters $F$, and output consisting of
the encodings of the dense clauses over $V$ variables whose single literal is at
$F(\mathsf{TW}) + u$, positive exactly when $u = a_c$, for $u = 0, \dots, n_1 - 1$, then of
those whose single literal is at $F(\mathsf{CB}) + y$, positive exactly when $y = e_a$, for
$y = 0, \dots, x$, then $o$.
