# The cell-shift tables of a machine are well formed

Let $M$ be a finite multi-stack Turing
machine with window depth $d$, let $E$ be an encoding of $M$ with $A_0$ label/state codes, $K$
stacks, $g$ symbol codes and $N$ situations, and let $H \ge d$. Then the table
$\mathrm{sa}(i) = A_0 + i$, the push counts $\mathrm{pl}$, the consumption counts $\mathrm{cn}$
and the pushed codes $\mathrm{pu}$ of $E$ are well formed for the cell-shift clauses of the layout
of $E$ with $N$ situations at height $H$: that is, $0 < g$, $d \le H$,
$\mathrm{sa}(i) < A_0 + N$ for all $i < N$, and for all $i < N$ and $k < K$ we have
$\mathrm{pl}(i, k) \le d$, $\mathrm{cn}(i, k) \le d$ and $\mathrm{pu}(i, k, j) < g$ for all
$j < \mathrm{pl}(i, k)$.
