# Progress condition for an edge

For a parity game with priorities, a partial assignment $\mu$ of tuples of $d + 1$ natural numbers to positions (an unassigned position standing for the top element) and any ordered pair of positions $v, w$ (the check does not inspect the moves, so no edge from $v$ to $w$ is required): if $v$ is unassigned, the condition holds; if $v$ is assigned and $w$ is not, it fails; and if $\mu(v) = a$ and $\mu(w) = b$, it requires $a \ge_p b$ when the priority $p$ of $v$ is even and $a >_p b$ when it is odd, in the lexicographic order truncated at $p$. When there is an edge from $v$ to $w$, this is the progress condition of a progress measure along that edge.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
