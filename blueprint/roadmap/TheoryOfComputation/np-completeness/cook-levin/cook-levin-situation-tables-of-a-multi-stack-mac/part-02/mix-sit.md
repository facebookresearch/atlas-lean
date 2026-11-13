# Mixed-radix index of a situation

Fix an encoding record $E$ of a finite multi-stack
machine $M$. Let $K$ be the number of stacks of $E$, $d$ the window depth of $M$, $A_0$ the number
of (label, state) codes of $E$, $g$ the symbol-code bound of $E$ and $N$ the number of situations.
For a code $c < A_0$ and window contents $w(k, j)$ with $w(k, j) < g$ for all $k < K$ and $j < d$,
let $i = \mathrm{mix}(g, c, K d, D)$ with digits $D(n) = w(\lfloor n / d \rfloor, n \bmod d)$.
Then $i < N$, $\mathrm{la}(i) = c$, and $\mathrm{wa}(i, k, j) = w(k, j)$ for all $k < K$ and
$j < d$.
