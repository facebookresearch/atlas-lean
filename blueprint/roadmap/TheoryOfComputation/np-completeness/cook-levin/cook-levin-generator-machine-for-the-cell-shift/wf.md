# Well-formed situation tables for the cell-shift family

Given a layout with label/state
block size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, a situation-offset table
$\mathrm{sa}$, push-count and consumed-count tables $\mathrm{pl}$ and $\mathrm{cn}$ and a
pushed-code table $\mathrm{pu}$, the tables are well formed for $N$ situations at height $H$ when
$g > 0$, $d \le H$, $\mathrm{sa}(i) < A$ for every $i < N$, and for all $i < N$ and $k < K$:
$\mathrm{pl}(i, k) \le d$, $\mathrm{cn}(i, k) \le d$, and $\mathrm{pu}(i, k, j) < g$ for every
$j < \mathrm{pl}(i, k)$.
