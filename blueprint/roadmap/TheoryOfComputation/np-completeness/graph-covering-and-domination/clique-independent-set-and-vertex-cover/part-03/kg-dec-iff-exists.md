# Verifying a graph language defined by a vertex-set condition

Let $m$ be a mode and
$P$ a property of a number $k$ and a graph on $n$ vertices. Suppose that for all $n$, $k$ and
every bit list $\mathit{bits}$ with one bit per pair $(i, j)$, $i < j < n$, the property $P$
holds for $k$ and the graph given by $\mathit{bits}$ exactly when some set of $k$ vertices meets
the pair condition of $m$ on every pair $i < j$. Then for every bit list $x$, $x$ belongs to
the language of instances satisfying $P$ if and only if the verifier for mode $m$ accepts $x$
with some witness $w$ of length $|w| \le |x|$.
