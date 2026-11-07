# C1a (decoding recovers a good configuration)

Let $E$ be an encoding of a machine $M$,
let $H \in \mathbb{N}$, and let $c$ be a good configuration of $M$ (every symbol on every stack
of $c$ lies in the effective alphabet of $E$) all of whose stacks have length at most $H$. Then
the row decoder of $E$ at height $H$, applied to the (label, state) code of $c$ and the cell
array of $c$, returns $c$.
