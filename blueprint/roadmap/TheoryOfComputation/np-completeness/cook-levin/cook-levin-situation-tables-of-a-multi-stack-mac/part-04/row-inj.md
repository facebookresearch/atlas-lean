# Good configurations are determined by their row (C1f)

Let $M$ be a finite multi-stack
Turing machine and $E$ an encoding of $M$ with $K$ numbered stacks, let $H \in \mathbb{N}$, and
for a configuration $c$ write $\mathrm{cell}(c, k, j)$ for the code of the symbol at depth $j$ of
the stack numbered $k$ ($0$ if there is none). Let $c$ and $c'$ be configurations that are good
for $E$ (every stack symbol lies in the effective alphabet of its stack) and all of whose stacks
have length at most $H$. If $c$ and $c'$ have the same (label, state) code and
$\mathrm{cell}(c, k, j) = \mathrm{cell}(c', k, j)$ for all $k < K$ and $j < H$, then $c = c'$.
