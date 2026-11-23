# One pass of the braid closure

Let $w$ be a braid word (a list of integers) of length $m$.
Starting from a traversal state, one pass applies the letters of $w$ in order as crossings, the
$k$-th letter (counting from $0$) occupying the slab $-(k+1) \le z \le -k$; this moves the state
to a strand position $p$ and appends the crossing vertices. It then appends the closure arc: the
vertices $(p, 100, -m)$ and $(p, 100, 0)$, followed by $(p, 0, 0)$ unless $p = 1$. The resulting
state has position $p$ and the extended vertex list.

When $p = 1$ the vertex $(1, 0, 0)$ is left out because the polyline starts there, so the closure
arc already returns to its first vertex.
