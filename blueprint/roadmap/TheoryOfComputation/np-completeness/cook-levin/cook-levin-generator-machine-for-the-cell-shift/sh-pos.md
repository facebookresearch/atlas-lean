# Literal positions of an in-range shift clause

For a layout $L$ with label block size $A$,
$K$ stacks and $g$ symbol codes, row width $W = A + K H g$, situation offsets $s_a$, push counts
$p$, consumed counts $c$ and numbers $H, t, i, k, u, x, l$, the position of literal $l$ of the
in-range shift clause $(t, i, k, u, x)$ is: if $l = 0$, the cell variable of row $t$, stack $k$,
depth $u + c(i, k)$ and symbol code $x$, namely $t W + A + (k H + u + c(i, k)) g + x$; if
$l = 1$, the situation variable $(t + 1) W + s_a(i)$; and if $l \ge 2$, the cell variable of row
$t + 1$, stack $k$, depth $u + p(i, k)$ and symbol code $x$, namely
$(t + 1) W + A + (k H + u + p(i, k)) g + x$.
