# Run of the code-clause chain of the accept generator

Let $F$ assign values to the
counters of the accept generator (for layout $L$ and parameters $n_1$, $\mathrm{ac}$, $k_1$,
$\mathrm{ea}$) such that the scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$
are $0$, $F(\mathrm{Vc}) = V$, $F(P) = 0$ and $F(\mathrm{TW}) + n_1 \le V$. Then for every
$u < n_1$, every output word $o$ and every Boolean state $v$, the generator runs in at most
$(u + 1)(V(3V + 6) + 10V + 13)$ steps from the first label of code clause $u$, with state $v$,
counters $F$ and output $o$, to the halting label $\mathrm{done}$, with state false, counters $F$
and output $w_0 w_1 \cdots w_u\, o$. Here $w_i$ is the encoding of the dense clause over $V$
variables whose only literal is variable $F(\mathrm{TW}) + i$, positive if and only if
$i = \mathrm{ac}$.
