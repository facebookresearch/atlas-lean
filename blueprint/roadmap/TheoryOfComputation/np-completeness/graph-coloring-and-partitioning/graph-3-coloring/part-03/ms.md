# Quiescent states of the 3-COLOR emitter

A quiescent state records the contents of
the token stack $T$ and of the stacks $D$, $E$, $A$, $P$ (lists of token symbols), the content
of the output stack $O$ (a list of bits), and four natural numbers $n$, $r$, $f$, $u$: the
values of the counters $N$ (next free vertex), $R$ (current OR output), $F$ (first-literal flag)
and $U$ (an earlier literal vertex).

On the machine, $N$, $R$, $F$, $U$ hold that many clause tokens $\mathtt{cl}$ and the scratch
stacks $X$, $B$, $W$ are empty.
