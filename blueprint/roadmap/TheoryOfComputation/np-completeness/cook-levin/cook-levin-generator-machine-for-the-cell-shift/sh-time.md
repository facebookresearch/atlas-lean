# Polynomial time bound for the shift generator

Let $L$ be a layout with label/state block
size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, let $\mathrm{sa}$, $\mathrm{pl}$,
$\mathrm{cn}$, $\mathrm{pu}$ be situation tables and let $N, T, H \in \mathbb{N}$, and suppose
the tables are well formed for $N$ situations at height $H$. Start the cell-shift generator for
$L$, $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ at its first
precomputation stage, in state false, with $T$ on the counter $\mathrm{Tn}$ and $H$ on the counter
$\mathrm{Hs}$ in unary, all other counters empty, and an arbitrary list $o$ of bits on the output
stack. Then within at most $c\,(T + H + 1)^6$ steps, where $c = 828\,(A + K + g + d + N + 1)^7$
is the constant of the shift-generator time bound for $L$ and $N$, it reaches its final label
$\mathrm{done}$, in some state, with stacks whose output stack holds the encoding of the
cell-shift clause family for $L$, $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$,
$N$, $T$ and $H$, followed by $o$.
