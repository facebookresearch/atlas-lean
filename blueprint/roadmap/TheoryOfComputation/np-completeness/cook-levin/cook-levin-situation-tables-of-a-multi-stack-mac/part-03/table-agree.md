# The table-driven step

Fix an encoding $E$ of a finite TM2 machine $M$, with $K$ stacks
and window depth $d$, and a natural number $H$. Let $c$ be a configuration such that every symbol
on every stack of $c$ lies in the effective alphabet of $E$ and every stack of $c$ has length at
most $H \mathbin{\dot{-}} d$ (truncated subtraction). Let $c'$ be the idle-extended step of $M$ at
$c$ and $i$ the situation index of $c$. Then the combined (label, state) code of $c'$ is the next
label/state code after situation $i$, and for all $k < K$ and $j < H$ the cell code of $c'$ on
stack number $k$ at depth $j$ is the value at $(k, j)$ of the table-driven row update with height
$H$ and situation $i$ applied to the cell codes of $c$.

No hypothesis $d \le H$ is needed: if $H < d$, every stack of $c$ is empty.
