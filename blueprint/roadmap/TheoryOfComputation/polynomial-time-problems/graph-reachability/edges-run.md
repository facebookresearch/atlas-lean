# The edge loop of a pass

Let $n$ be a natural number, $es$ a list of arcs $(u, w)$ of
natural numbers and $m$ a list of $n$ Boolean marks. Encode an arc $(u, w)$ by $u$ ones, a zero,
$w$ ones and a zero, and $es$ by the concatenation of the codes of its arcs; let $\ell$ be the
length of this code. Suppose the marking machine is at the edge-loop label, in any internal state,
with stacks $S$ such that the input stack $X$ holds the code of $es$ and the mark stack $M$ holds
$m$ (vertex $0$ on top), as bit symbols, and the parked-mark stack $P$ and the arc counters $U$
and $V$ are empty. Then within $4\ell + 1$ steps it reaches the pass-loop label with stacks $S'$
in which $X$ is empty, the edge stack $E$ holds the code of $es$ in reverse order on top of its
contents in $S$, $M$ holds the marks that one pass of the marking algorithm with $n$ vertices over
$es$ (Mark Pass) produces from $m$, and $P$, $U$, $V$ are empty; every stack other than $X$, $E$,
$M$, $U$, $V$ and $P$ holds the same list in $S'$ as in $S$.
