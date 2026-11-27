# Literal positions of an overflow clause

For a layout $L$ with label block size $A$, $K$
stacks and $g$ symbol codes, row width $W = A + K H g$, situation offsets $s_a$, push counts $p$,
consumed counts $c$ and numbers $H, t, i, k, r, l$, the position of literal $l$ of the overflow
clause $(t, i, k, r)$ is the situation variable $(t + 1) W + s_a(i)$ if $l = 0$, and otherwise the
cell variable of row $t + 1$, stack $k$, depth $H - c(i, k) + p(i, k) + r$ and symbol code $0$,
namely $(t + 1) W + A + (k H + H - c(i, k) + p(i, k) + r) g$. Subtraction is truncated at $0$.
