# Costed progress check for an edge

For a parity game on $n$ positions with priorities, a partial assignment $\mu$ of tuples of $d + 1$ natural numbers to positions (a position may be unassigned, standing for the top value), and an edge from $v$ to $w$: if $v$ is unassigned the check succeeds at cost $0$; if $v$ is assigned and $w$ is not, it fails at cost $0$; and if $\mu(v) = a$ and $\mu(w) = b$, it is the costed non-strict truncated comparison of $a$ and $b$ at threshold the priority of $v$ when that priority is even, and the costed strict one when it is odd, each atomic comparison costing $1$.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301.
