# Explicit time bound of the accept generator

For a layout $L$ with label block size $A$,
$K$ stacks and $g$ symbol codes, and natural numbers $n_1$, $k_1$, $T$, $H$, let
$W = A + K H g$ and $V = (T + 1) W$ (the number of variables). The bound is $P + (g + n_1)\,C$,
where $C = V(3V + 6) + 10V + 13$ is the cost of one clause and the precomputation cost is
$P = 3 + (H(2g + 3) + H + 2) + (K(2Hg + 3) + K + 2) + (T(2W + 3) + T + 2) + 1 +
((T + 1)(2W + 3) + (T + 1) + 2) + (2TW + 2) + 2 + (k_1(2Hg + 3) + k_1 + 2)$.

It is at most $314\,(A + K + g + n_1 + k_1 + 1)^5\,(T + H + 1)^4$.
