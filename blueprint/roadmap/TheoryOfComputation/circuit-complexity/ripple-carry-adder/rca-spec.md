# Gate-value specification of the ripple-carry adder

Let $x, y$ be $n$-bit vectors, $c$ a
bit and $j$ a natural number, and write $j = 5i + r$ with $0 \le r < 5$. Let $x_i$ and $y_i$ be
bit $i$ of $x$ and $y$ (bit $0$ is the least significant, and bits at positions $i \ge n$ are $0$),
and let $c_i$ be the carry into position $i$ when $x$, $y$ and $c$ are added: reading $x$ and $y$
as natural numbers, $c_i = 1$ exactly when $(x \bmod 2^i) + (y \bmod 2^i) + c \ge 2^i$. The
specification assigns to $j$ the bit $x_i \oplus y_i$ if $r = 0$, $(x_i \oplus y_i) \oplus c_i$
if $r = 1$, $x_i \wedge y_i$ if $r = 2$, $(x_i \oplus y_i) \wedge c_i$ if $r = 3$, and $c_{i+1}$
if $r = 4$.
