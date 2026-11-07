# The `TM2` SAT verifier

For a flag $\mathit{cap}$, the host machine with that flag computes
the host's answer in polynomial time. For every pair $(x, w)$ of bit lists, started on the input
$x \# w$ (the bits of $x$, a separator, then the bits of $w$), it halts with the single bit
$\mathrm{ans}_{\mathit{cap}}(x, w)$ on its output stack and every other stack empty within $T(n)$
steps, where $n$ is the length of $x \# w$ and $T$ is the host's polynomial step bound. Here
$\mathrm{ans}_{\mathit{cap}}(x, w)$ is false unless $x$ decodes to a CNF formula $\varphi$; in that
case it is true exactly when $\varphi$ passes the clause check against the table built from $w$
and, if $\mathit{cap}$ is true, every clause of $\varphi$ has at most three literals.
