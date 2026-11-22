# Overflow forcing

Let $L$ be a layout with $K$ stacks, let $\mathrm{sa}$, $\mathrm{pl}$,
$\mathrm{cn}$ and $\mathrm{pu}$ be situation tables, and let $a$ be an assignment satisfying the
cell-shift clause family of $L$ and these tables for bounds $N$, $T$ and $H$. Write $X[t, b]$ and
$C[t, k, j, x]$ for the label/state and cell variables at height $H$. If $t < T$, $i < N$,
$k < K$, $r < \mathrm{cn}(i, k) - \mathrm{pl}(i, k)$ and the situation variable
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$, then the variable
$C[t + 1, k, H - \mathrm{cn}(i, k) + \mathrm{pl}(i, k) + r, 0]$ is true under $a$, where symbol
code $0$ is the empty cell. Subtraction is truncated at zero.
