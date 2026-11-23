# Adding a literal occurrence in the 3-COLOR construction

Given a literal $l = (x, b)$
with variable index $x$ and polarity $b$, and a state whose next free vertex is $n$, let $L = n$
and $M = n + 1$. The new state has next free vertex $n + 2$, records the occurrence
$(x, b, L, M)$ at the front of the list of earlier occurrences, and appends to the emitted edges
first $(L, M)$, $(L, 2)$, $(M, 2)$ (a triangle with the palette vertex $2$), then the
consistency edges of the new occurrence $(L, M)$ of $l$ with each earlier occurrence, taken
latest first. The result is this new state together with the vertex $L$.
