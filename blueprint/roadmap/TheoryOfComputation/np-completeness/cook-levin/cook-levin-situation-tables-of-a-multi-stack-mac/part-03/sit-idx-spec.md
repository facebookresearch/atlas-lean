# The situation index matches the code and windows

Fix an encoding $E$ of a finite TM2
machine $M$, with $K$ stacks, $N$ situations and window depth $d$. If every symbol on every stack
of a configuration $c$ lies in the effective alphabet of $E$, then the situation index $i$ of $c$
satisfies $i < N$, the label/state code of situation $i$ equals the combined (label, state) code
of $c$, and for all $k < K$ and $j < d$ the window symbol code of situation $i$ on stack $k$ at
depth $j$ equals the cell code of $c$ on stack number $k$ at depth $j$.
