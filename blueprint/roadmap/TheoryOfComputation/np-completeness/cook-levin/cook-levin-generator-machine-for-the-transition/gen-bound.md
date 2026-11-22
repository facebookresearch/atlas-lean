# Time bound of the generator

For a layout $L$ and $N, T, H \in \mathbb{N}$, the time
bound of the whole generator is $P + T(B + 1) + T + 2$, where $P$ is the time bound of the
precomputation for $L$, $T$ and $H$, and $B$ is the time bound of one iteration of the time loop
for $L$, $N$, $T$ and $H$.

It is at most $C\,(T + H + 1)^5$ for a constant $C$ depending only on $L$ and $N$ (see the
[polynomial time bound](gen-time.md)).
