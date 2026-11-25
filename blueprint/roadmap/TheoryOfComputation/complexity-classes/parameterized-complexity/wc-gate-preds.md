# Predecessors of an encoded gate

The predecessor list of an encoded gate $(k, r)$ is $r$
when $k$ is $2$, $3$ or $4$ (a NOT, AND or OR gate), and the empty list for every other kind.

Variable (kind $0$) and constant (kind $1$) payloads are a variable index and a constant value,
not predecessor gates; folding over them would attribute unrelated gates' weft or depth (for
example, an input gate $(0, [0])$ inheriting gate $0$'s depth).
