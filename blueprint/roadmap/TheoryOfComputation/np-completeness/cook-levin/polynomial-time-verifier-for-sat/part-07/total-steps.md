# Explicit step bound of the SAT verifier machine

For a flag $\mathit{cap}$ and an input
length $N$, let $s(N) = (2N + 5) + (2N + 2) + (2N + 2) + (N(8N + 9) + 1)$ be the number of
steps allowed before the cleanup, and let $p$ be the per-step push budget of the host machine
with that flag. The total step bound is $s(N) + (N + p \cdot s(N)) + 2$.

When the cleanup starts, every stack has length at most $N + p \cdot s(N)$; the cleanup and the
output step then take at most that many steps plus $2$.
