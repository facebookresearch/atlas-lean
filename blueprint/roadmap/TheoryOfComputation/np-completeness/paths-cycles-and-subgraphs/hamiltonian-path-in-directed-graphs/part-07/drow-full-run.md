# The row of a diamond in the HAMPATH emitter

Let $B$, $m$ and $i$ be natural numbers,
write $\tau = m + i(3m+2)$ for the top vertex of diamond $i$ and $\rho_l = \tau + 1 + l$ for its
row vertices, and encode an arc $(a, b)$ by the bits $1^a 0 1^b 0$. Let $s$ be a quiescent state
of the emitter whose counters satisfy $P = \tau$, $M = 3m$, $L = 0$, $R = 0$, $N \le B$,
$J \le B$ and $D \le B$, and suppose $\rho_{3m} \le B$. Then for every internal bit $v$ there is
an internal bit $v'$ such that the emitter goes, in at most $B(8B+15) + 2B + 5$ steps, from label
$\mathsf{r0}$ with bit $v$ and the stacks of $s$ to label $\mathsf{e0}$ with bit $v'$ and the
stacks of the state obtained from $s$ by setting $R = \rho_{3m}$ and appending to its edge bits
the codes of the arcs $(\rho_l, \rho_{l+1})$ and $(\rho_{l+1}, \rho_l)$ for $l = 0, \dots, 3m-1$,
in this order.
