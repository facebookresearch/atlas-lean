# One iteration of the in-range loop of the cell-shift generator

Let $L$ be a layout with
label block size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, let $T, H \in \mathbb{N}$,
let $W = A + K H g$ be the row width and $V = (T + 1) W$ the number of variables, and let the
situation-offset, push-count, consumed-count and pushed-code tables $s_a, p, c, p_u$ be well
formed for $N$ situations and height $H$. Let $t < T$, $i < N$, $k < K$ and $u \in \mathbb{N}$
with $u + \max(p(i, k), c(i, k)) < H$. Let $F$ be counter values in which $\mathrm{Q}$,
$\mathrm{tmp}$, $\mathrm{md}$, $\mathrm{c1}$, $\mathrm{c2}$, $\mathrm{P}$, $\mathrm{CB}$ and
$\mathrm{CW}$ are $0$, $F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(\mathrm{Wc}) = W$,
$F(\mathrm{TW}) = t W$, $F(\mathrm{TW1}) = (t + 1) W$, $F(\mathrm{KB}) = k H g + t W + A$ and
$F(\mathrm{U}) = u$. Then for every output word $o$ and flag $v$, the generator for these data,
started at the in-range variant of the first loop-body stage $\mathrm{bC1}$ of block $(i, k)$
with flag $v$, counters $F$ and output $o$, reaches the in-range loop head $\mathrm{sHead}$ of
block $(i, k)$ with flag false, counters $F$ and output $e_0 e_1 \cdots e_{g-1}$ followed by $o$
in at most $3(2V + 2) + (H(2g + 3) + H + 2) + g B(V) + 2(V + 1)$ steps, where
$B(V) = V(3V + 6) + 3(6V + 9) + 3V + 4$ is the step budget of one clause and $e_x$ is the
encoding of the dense clause over $V$ variables whose literals are the in-range shift literals
for $(t, i, k, u, x)$.
