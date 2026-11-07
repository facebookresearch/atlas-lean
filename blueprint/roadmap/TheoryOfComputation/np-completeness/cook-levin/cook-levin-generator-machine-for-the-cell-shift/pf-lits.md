# Literals of a pushed-fill clause

For a layout $L$ with label block size $A$, $K$ stacks
and $g$ symbol codes, row width $W = A + K H g$, situation offsets $s_a$, pushed codes $p_u$ and
numbers $H, t, i, k, j$, write $S[t, i] = (t + 1) W + s_a(i)$ for the situation variable (the
label/state variable $s_a(i)$ of row $t + 1$), and
$C[t', k', j', x] = t' W + A + (k' H + j') g + x$ for the cell variable of row $t'$, stack $k'$,
depth $j'$ and symbol code $x$. The pushed-fill clause $(t, i, k, j)$ is the list of two
(variable, sign) literals $\neg S[t, i] \lor C[t + 1, k, j, p_u(i, k, j)]$: first the negated
situation variable $S[t, i]$, then the positive cell variable of row $t + 1$, stack $k$, depth
$j$ and symbol code $p_u(i, k, j)$. It is used for depths $j$ below the number of symbols that
situation $i$ pushes on stack $k$.
