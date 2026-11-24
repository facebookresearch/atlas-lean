# The HAMPATH instance as unary blocks and arc bits

Let $\varphi$ be a CNF formula with $m$
clauses and $k$ distinct variables, and let $t = m + k(3m + 2)$ be the top of diamond $k$. Then
the HAMPATH instance of $\varphi$ is the bit string made of $m$ ones and a zero (the start
vertex $s = m$), then $t$ ones and a zero (the target vertex $t$), then $t + 1$ ones and a zero
(the vertex count $n = t + 1$), followed by the arcs of the construction, each arc $(u, v)$
written as $u$ ones, a zero, $v$ ones and a zero.
