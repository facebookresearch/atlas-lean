# The situation-definition tables of a machine are well formed

Let $M$ be a finite
multi-stack Turing machine with window depth $d$, let $E$ be an encoding of $M$ with $A_0$
label/state codes, $K$ stacks, $g$ symbol codes and $N$ situations, and let $H \ge d$. For every
situation $i < N$, the current-code table $\mathrm{la}$ of $E$, the table
$\mathrm{sa}(i) = A_0 + i$ as next-code table and the window table $\mathrm{wa}$ of $E$ are well
formed for the transition clauses of the layout of $E$ at situation $i$ and height $H$: that is,
$\mathrm{la}(i) < A_0 + N$, $\mathrm{sa}(i) < A_0 + N$, $\mathrm{wa}(i, k, j) < g$ for all
$k < K$ and $j < d$, and $d \le H$.
