# Literals of an overflow clause

For a layout $L$ with label block size $A$, $K$ stacks and
$g$ symbol codes, row width $W = A + K H g$, situation offsets $s_a$, push counts $p$, consumed
counts $c$ and numbers $H, t, i, k, r$, write $S[t, i] = (t + 1) W + s_a(i)$ for the situation
variable (the label/state variable $s_a(i)$ of row $t + 1$), and
$C[t', k', j, x] = t' W + A + (k' H + j) g + x$ for the cell variable of row $t'$, stack $k'$,
depth $j$ and symbol code $x$. The overflow clause $(t, i, k, r)$ is the list of two (variable,
sign) literals $\neg S[t, i] \lor C[t + 1, k, H - c(i, k) + p(i, k) + r, 0]$: first the negated
situation variable $S[t, i]$, then the positive cell variable of row $t + 1$, stack $k$, depth
$H - c(i, k) + p(i, k) + r$ and symbol code $0$ (the empty cell). Subtraction is truncated at
zero.
