# One iteration of the overflow loop of the cell-shift generator

Let $L$ be a layout with
label block size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, let $W = A + K H g$ be the
row width and $V = (T + 1) W$ the number of variables, and let the tables $s_a, p, c, p_u$ be well
formed for $N$ situations and height $H$. Let $t < T$, $i < N$, $k < K$ and
$r < c(i, k) - p(i, k)$. Let $F$ be counter values in which $\mathrm{Q}$, $\mathrm{tmp}$,
$\mathrm{md}$, $\mathrm{c1}$, $\mathrm{c2}$, $\mathrm{P}$, $\mathrm{Ka}$, $\mathrm{CB}$ and
$\mathrm{CW}$ are $0$, $F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(\mathrm{Wc}) = W$,
$F(\mathrm{TW}) = t W$, $F(\mathrm{TW1}) = (t + 1) W$, $F(\mathrm{KB}) = k H g + t W + A$,
$F(\mathrm{U}) = H - \max(p(i, k), c(i, k))$ and $F(\mathrm{R}) = r$. Then for every output word
$o$ and flag $v$, the generator for these data, started at stage $\mathrm{oC1}$ of block $(i, k)$
with flag $v$, counters $F$ and output $o$, reaches stage $\mathrm{oHead}$ of block $(i, k)$ with
flag false, counters $F$ and output $e$ followed by $o$ in at most
$\mathrm{oBodyB}(g, H, d, V) = 3 V^2 + 35 V + 2 g H + 7 H + 2 d + 46$ steps, where $e$ is the
encoding of the dense clause over $V$ variables whose literals are those of the overflow clause
$(t, i, k, r)$.
