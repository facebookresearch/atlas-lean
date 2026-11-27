# One clause of the accept generator

Let $L$ be a layout with $g$ symbol codes, let
$n_1, a, k_1, e, V \in \mathbb{N}$, and let $c$ be a clause kind of the accept generator (a code
clause $u < n_1$ or a cell clause $x < g$) with base counter $b(c)$, offset $\mathrm{off}(c)$ and
polarity $\sigma(c)$ for $a$ and $e$. Let $F$ be counter values of the generator whose scratch
counters $\mathsf{Q}$, $\mathsf{tmp}$, $\mathsf{md}$, $\mathsf{c1}$, $\mathsf{c2}$ are $0$, with
$F(\mathsf{Vc}) = V$, $F(\mathsf{P}) = 0$ and $p = F(b(c)) + \mathrm{off}(c) < V$. Then for every
output word $o$ and every Boolean state $v$, the accept generator for $L$, $n_1$, $a$, $k_1$, $e$
runs in at most $V(3V + 6) + 10V + 13$ steps from the label $\mathrm{e00}(c)$, with state $v$,
counters $F$ and output $o$, to the label after clause $c$, with state false, the same counters
$F$, and output the encoding of the dense clause over $V$ variables whose only literal is the
variable $p$ with polarity $\sigma(c)$, followed by $o$.
