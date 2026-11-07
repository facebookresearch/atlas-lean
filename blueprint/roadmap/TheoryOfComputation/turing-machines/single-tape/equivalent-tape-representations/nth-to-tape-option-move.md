# Cells after an optional move

For an optional direction $d$, let $\delta(d)$ be $0$ if $d$
is no move, $-1$ if $d$ is a move to the left and $1$ if $d$ is a move to the right. For every
two-way tape $t$ over $\Gamma$ and every integer $i$, the cell at position $i$ of the view of the
tape obtained from $t$ by the optional move $d$ is the cell at position $i + \delta(d)$ of the view
of $t$.
