# Out-of-range arcs need no guard

Let $m$ be a list of $n$ Boolean marks and let $u$, $v$
be natural numbers; write $m_u$ for the entry of $m$ at position $u$ (counting from $0$), taken to
be false when $u \ge n$. If $u < n$, $v < n$ and $m_u$ is true, set position $v$ of $m$ to true,
and otherwise keep $m$; the result is the same as setting position $v$ of $m$ to true when $m_u$ is
true and keeping $m$ otherwise.

Setting a position $v \ge n$ leaves the list unchanged, so the machine, which reads the mark of $u$
and then sets the mark of $v$, ignores an arc with an end past the last vertex, as the marking
algorithm does.
