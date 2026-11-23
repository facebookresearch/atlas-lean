# Edge-loop verdict after one parsed edge

Let $cs$ be a list of color codes and $r$ a bit
list. If $r$ begins with $u$ in unary ($u$ ones, then a zero) followed by the rest $r_1$, and
$r_1$ begins with $v$ in unary followed by the rest $r_2$, then the edge-loop verdict on $r$ with
vertex colors $cs$ holds iff the edge verdict for $(u, v)$ holds and the edge-loop verdict on
$r_2$ holds.
