# Progress condition for an edge

For a parity game with priorities, a partial assignment $\mu$ of tuples of $d + 1$ natural numbers to positions (an unassigned position standing for the top element) and an edge from $v$ to $w$: if $v$ is unassigned, the condition holds; if $v$ is assigned and $w$ is not, it fails; and if $\mu(v) = a$ and $\mu(w) = b$, it requires $a \ge_p b$ when the priority $p$ of $v$ is even and $a >_p b$ when it is odd, in the lexicographic order truncated at $p$.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301.
