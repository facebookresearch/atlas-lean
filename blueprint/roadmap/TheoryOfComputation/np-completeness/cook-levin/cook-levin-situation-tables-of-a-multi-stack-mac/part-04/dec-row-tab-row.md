# C2' (decoding the table-driven row gives the next configuration)

Let $E$ be an encoding
of a machine $M$ with window depth $d$, let $H \ge d$ be a natural number, and let $c$ be a good
configuration of $M$ (every symbol on every stack of $c$ lies in the effective alphabet of $E$)
all of whose stacks have length at most $H - d$. Let $i$ be the situation index of $c$. Then the
row decoder of $E$ at height $H$, applied to the next (label, state) code of situation $i$ and to
the table-driven row update at height $H$ of situation $i$ on the cell array of $c$, returns the
idle-extended step of $c$: the configuration after one step of $M$, or $c$ itself if $c$ is
halted.
