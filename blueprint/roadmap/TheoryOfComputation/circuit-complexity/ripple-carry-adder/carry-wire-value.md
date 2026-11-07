# Value of the carry wire

Let $x$ and $y$ be $n$-bit vectors, $c$ a bit, and $i$ and $g$
natural numbers with $5i \le g$. Suppose the first $g$ gates are given values $v_0, \dots, v_{g-1}$
with each $v_j$ equal to the specified value of gate $j$ of the adder on $x$, $y$, $c$. Then, on
the adder input for $x$, $y$, $c$ and with these gate values, the carry wire into bit $i$ carries
the carry into bit $i$ of $x + y + c$: it is true exactly when
$(x \bmod 2^i) + (y \bmod 2^i) + c \ge 2^i$, reading $x$, $y$ and $c$ as natural numbers.
