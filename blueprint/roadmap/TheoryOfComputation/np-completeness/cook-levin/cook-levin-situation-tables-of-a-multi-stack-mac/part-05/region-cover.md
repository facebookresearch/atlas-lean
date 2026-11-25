# The three depth regions cover every depth exactly once

Let $p, q, H, j$ be natural
numbers with $j < H$, and let $m = H - \max(p, q) + p$, where the subtraction is truncated at
$0$. Then $j$ lies in exactly one of the ranges $j < p$ (pushed fill), $p \le j < m$ (in-range
shift) and $m \le j < H$ (overflow).

These are the depth hypotheses of the pushed-fill, in-range shift and overflow lemmas; nothing is
assumed about $p$, $q$ and $H$.
