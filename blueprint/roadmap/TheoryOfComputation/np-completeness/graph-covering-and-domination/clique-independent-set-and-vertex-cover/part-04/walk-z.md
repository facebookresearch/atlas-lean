# Rest of a walk step of the clique verifier

Write $\mathrm{free}_m(s)$ for the condition
that, in mode $m$, a vertex with chosen-flag $s$ settles every pair of its row, and
$\mathrm{sat}_m(b', s')$ for the pair condition on pair bit $b'$ and later vertex flag $s'$. In
mode $m$ with row flag $c$, after a bit $z$ has been popped off the vertex stack $V$: if $V$ is
now empty, the machine moves to the put-back label when $\mathrm{free}_m(z)$ or $c$ holds, and to
the reject label otherwise. If $V$ is not empty, it pushes $z$ onto the scratch stack $T$; then
it moves to the reject label if the input stack $X$ is empty, and otherwise pops the top symbol
of $X$, reads it as a bit $b$ (a non-bit symbol reads as false), and moves to the walk label
with flag $c \wedge \mathrm{sat}_m(b, z)$.
