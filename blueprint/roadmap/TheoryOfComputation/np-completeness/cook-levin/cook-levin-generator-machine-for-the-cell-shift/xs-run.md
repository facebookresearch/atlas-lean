# The in-range chain of the cell-shift generator

Let $L$ be a layout with label block size
$A$, $K$ stacks, $g$ symbol codes and window depth $d$, let $H, T \in \mathbb{N}$, let
$W = A + K H g$ be the row width and $V = (T + 1) W$ the number of variables, and let the tables
$\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ be well formed for $N$ situations and height
$H$: $g > 0$, $d \le H$, and for all $i < N$ and $k < K$, $\mathrm{sa}(i) < A$,
$\mathrm{pl}(i, k) \le d$, $\mathrm{cn}(i, k) \le d$ and $\mathrm{pu}(i, k, j) < g$ for every
$j < \mathrm{pl}(i, k)$. Let $t < T$, $i < N$, $k < K$ and $u \in \mathbb{N}$ with
$u + \max(\mathrm{pl}(i, k), \mathrm{cn}(i, k)) < H$, let $b = k H g + t W + A$ be the first
cell variable of stack $k$ in row $t$, and let $F$ be counter values in which $\mathrm{Q}$,
$\mathrm{tmp}$, $\mathrm{md}$, $\mathrm{c1}$, $\mathrm{c2}$ and $\mathrm{P}$ are $0$,
$F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(\mathrm{Wc}) = W$, $F(\mathrm{TW}) = t W$,
$F(\mathrm{TW1}) = (t + 1) W$, $F(\mathrm{CB}) = u g + b$ and $F(\mathrm{CW}) = u g + b + W$.
Then for every $n \le g$, every output word $o$ and every flag $v$ there is a flag $v'$ such that
the generator for these data, started at the entry label of the in-range chain for $n$ in block
$(i, k)$ with flag $v$, counters $F$ and output $o$, reaches the in-range drain stage
$\mathrm{dCB}$ of block $(i, k)$ with flag $v'$, counters $F$ and output $e_0 e_1 \cdots e_{n-1}$
followed by $o$ in at most $n \cdot \mathrm{clauseB}(V)$ steps, where
$\mathrm{clauseB}(V) = V(3V + 6) + 3(6V + 9) + 3V + 4$ and $e_x$ is the encoding of the dense
clause over $V$ variables whose literals are the in-range shift literals for $(t, i, k, u, x)$.
