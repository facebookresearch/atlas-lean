# The carry out of a block of bits

Let $x, y$ be $n$-bit vectors and $c$ a carry-in bit,
and for $i \in \mathbb{N}$ let $c_i$ be the carry into bit $i$ when computing $x + y + c$, that
is, $c_i$ holds exactly when $(x \bmod 2^i) + (y \bmod 2^i) + c \ge 2^i$, where $x$, $y$ are
read as natural numbers and $c$ counts as $1$ when true. For all $a, \ell \in \mathbb{N}$, if
$(G, P)$ are the generate and propagate signals of the block of bits $a, \dots, a + \ell - 1$,
then $c_{a + \ell} = G \lor (P \land c_a)$.
