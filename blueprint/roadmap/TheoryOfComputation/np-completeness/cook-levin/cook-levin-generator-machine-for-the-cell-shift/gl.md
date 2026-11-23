# Labels of the cell-shift generator

For natural numbers $N$, $K$, $g$ and $d$, a label is
one of: a precomputation stage $\mathrm{pre}(s)$; a time-loop label $\mathrm{tHead}$,
$\mathrm{tRest}$, $\mathrm{tw}(s)$ for a multiplication stage $s$, $\mathrm{t1a}$,
$\mathrm{t1b}$, $\mathrm{t1c}$, $\mathrm{t1d}$, $\mathrm{tEnd}$ or $\mathrm{tEnd2}$; a setup or
loop stage $\mathrm{s}(i, k, x)$ of the block of situation $i < N$ and stack $k < K$; a decrement
step $\mathrm{sb}(i, k, r)$ with $r < d + 1$; a loop-body stage $\mathrm{b}(i, k, x)$ of that
block, over clause kinds with parameters $g$ and $d$; or a halting label $\mathrm{bad}$ or
$\mathrm{done}$.
