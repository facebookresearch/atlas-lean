# Generator output after part of the time loop

For a layout $L$, tables $la$, $na$, $wa$,
sizes $N$, $T$, $H$, a number $m$ of iterations and a Boolean list $o$, the output after $m$
iterations is the concatenation, over the $m$ consecutive time steps $s$ starting at $T - m$ in
increasing order, of the encoded clauses of time step $s$, followed by $o$. Here $T - m$ is
truncated subtraction, so for $m \le T$ these are the time steps $T - m, \dots, T - 1$.
